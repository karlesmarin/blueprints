# encaje: laboratorio principal del blueprint relay-floors, «Check your link»; Python puro (Pyodide). Usa relay_floor
# (cota reforzada y recíproca, Props. 7.2–7.3) y relay_lindblad (pulso de tiempo mínimo); comprobado en prueba_lab.py.
"""run_link: check and validate a qubit -> bus mode -> qubit link with the floors of the paper.

The reader gives the maximal couplings and the coherence times of each element (and, if known, the measured error and
the pulse duration). The lab returns the floor on 1 - F_B for EVERY pulse, the relaxation-only floor, the error of the
minimal-time pulse (Lindblad), a verdict on the measured error, and which hardware change lowers the floor most; each
result with its explanation in words. Figures: the bound against the duration (forbidden region hatched), the design
bars, and the bound as a surface over (duration, coupling) with the measured point above it.
"""
import json
import math
import random

import labkit as K
import relay_floor as RF
import relay_lindblad as RL

E4 = 1e4          # errors are shown in units of 1e-4
COL_MIN, COL_SEQ, COL_MEAS = '#1B6F8C', '#C62828', '#111111'
COL_AD = ['#A5D6A7', '#66BB6A', '#2E7D32', '#1B5E20']      # adiabatic 2×, 4×, 8×, 16×


def _f(x, nd=2):
    return ('%.' + str(nd) + 'f') % x


def _read(params):
    p = json.loads(params) if isinstance(params, str) else params
    val = lambda k, d: float(str(p.get(k, d)).strip() or d)
    ga = val('ga_mhz', 9)
    gb_txt = str(p.get('gb_mhz', '')).strip()
    gb = float(gb_txt) if gb_txt else ga
    qa = (val('t1a', 99.7), val('t2a', 7.1))
    bus = (val('t1c', 38.6), val('t2c', 51.0))
    qb = (val('t1b', 112.6), val('t2b', 60.0))
    m = str(p.get('measured', '')).strip()
    tg = str(p.get('tg_ns', '')).strip()
    return ga, gb, qa, bus, qb, (float(m) if m else None), (float(tg) if tg else None)


def _unc(params):
    """(σ of the measurement ×10⁻⁴, ± % on every coherence time, ± % on the couplings); blanks are 0."""
    p = json.loads(params) if isinstance(params, str) else params
    v = lambda k: float(str(p.get(k, '') or '0').strip() or 0)
    return v('sigma'), v('unc_t'), v('unc_g')


def _corner(qa, bus, qb, ga, gb, ut, ug, sign):
    """The link with every time and coupling moved by ± ut %, ± ug % (sign +1: the most favourable corner, the
    lowest bound, since the bound does not rise when a time or a coupling grows; checked in prueba_robusta.py)."""
    ft, fg = 1 + sign * ut / 100, 1 + sign * ug / 100
    sc = lambda e: (e[0] * ft, e[1] * ft)
    return sc(qa), sc(bus), sc(qb), ga * fg, gb * fg


def _check(ga, gb, qa, bus, qb, meas, tg):
    for g in (ga, gb):
        if not 0.05 <= g <= 500:
            return 'couplings g/2π between 0.05 and 500 MHz'
    for name, (t1, t2) in (('qubit A', qa), ('bus mode', bus), ('qubit B', qb)):
        if not (0.01 <= t1 <= 1e6 and 0.01 <= t2 <= 1e6):
            return '%s: T1 and T2 between 0.01 and 10⁶ µs' % name
        if t2 > 2 * t1 * (1 + 1e-9):
            return '%s: T2 cannot exceed 2 T1 (the pure dephasing rate 1/T2 − 1/(2T1) would be negative)' % name
    if meas is not None and not 0 < meas < 1e4:
        return 'measured error 1 − F_B in units of 10⁻⁴, between 0 and 10⁴'
    if tg is not None and not 0.1 <= tg <= 1e6:
        return 'pulse duration between 0.1 and 10⁶ ns'
    return None


def _design(ga, gb, qa, bus, qb):
    """Floor after one hardware change at a time (T2 capped at 2 T1)."""
    cap = lambda e, t2: (e[0], min(t2, 2 * e[0]))
    out = [('2 × coupling g', RF.floor(qa, bus, qb, 2 * ga, 2 * gb)[0]),
           ('2 × T2 of qubit A', RF.floor(cap(qa, 2 * qa[1]), bus, qb, ga, gb)[0]),
           ('2 × T2 of qubit B', RF.floor(qa, bus, cap(qb, 2 * qb[1]), ga, gb)[0]),
           ('2 × T1 of qubit A', RF.floor((2 * qa[0], qa[1]), bus, qb, ga, gb)[0]),
           ('2 × T1 of qubit B', RF.floor(qa, bus, (2 * qb[0], qb[1]), ga, gb)[0]),
           ('2 × T1 of the bus mode', RF.floor(qa, (2 * bus[0], bus[1]), qb, ga, gb)[0]),
           ('bus without pure dephasing', RF.floor(qa, (bus[0], 2 * bus[0]), qb, ga, gb)[0])]
    return sorted(out, key=lambda kv: kv[1])


def _hypotheses():
    return ('Check, in this order: (1) the coupling: a larger maximal coupling than declared, or several bus modes '
            'used at once (the bound holds with G the norm of each qubit’s coupling vector); (2) the coherence times '
            'at the flux point of the transfer, not at the idle point; (3) dephasing that is not Markovian (slow noise, '
            'T2E > T2*): the floor assumes the Ramsey T2* as a Markovian rate; (4) the metric: the floor bounds the '
            'average fidelity of the channel at B, 1 − F_B, not a process fidelity or a readout-corrected number; '
            '(5) the initial state: B and the bus must start empty.')


def _pulses(gmin, qa, bus, qb, tmin):
    """The simple pulses of the relay sphere: minimal time, two sequential swaps, and adiabatic (STIRAP-like) pulses of
    increasing duration. Returns [(name, T in µs, 1 - F_B, trajectory)]."""
    G = 2 * math.pi * gmin
    steps = lambda T: int(min(2500, max(300, 14 * G * T)))
    out = []
    for name, (g, T) in (('minimal-time pulse', RL.pulse_minimal(G)), ('two sequential swaps', RL.pulse_sequential(G))):
        e, tr = RL.evolve(g, T, qa, bus, qb, steps=steps(T))
        out.append((name, T, e, tr))
    for f in (2, 4, 8, 16):
        g, T = RL.pulse_adiabatic(G, f * tmin)
        e, tr = RL.evolve(g, T, qa, bus, qb, steps=steps(T))
        out.append(('adiabatic pulse, %g × the minimal time' % f, T, e, tr))
    return out


def _sphere(pulses, floor_v):
    """3D: the relay sphere. The point (|a|, |b|, |c|) of the excitation: qubit A and qubit B on the floor, the bus
    upwards; without losses it stays on the unit sphere, and the radius it loses is what the transfer loses. The
    quarter circle on the floor is the dark-state path (bus empty). A slider over the duration of the adiabatic pulse
    shows the trade-off behind the floor: slow pulses hug the floor but shrink (qubit decay); fast ones climb into the
    bus and shrink there (bus loss)."""
    q = math.pi / 2
    shell = K.surface3(lambda u, v: [math.cos(u) * math.sin(v), math.sin(u) * math.sin(v), math.cos(v)],
                       [q * k / 14 for k in range(15)], [q * k / 14 for k in range(15)],
                       name='no loss: the unit sphere', color='#d9e6f2', opacity=0.25)
    dark = K.curve3([[math.cos(q * k / 40), math.sin(q * k / 40), 0.0] for k in range(41)],
                    name='dark-state path (bus empty)', color='#6A1B9A', width=3, dash=True)
    corners = [K.points3([[1, 0, 0]], name='qubit A (start)', color='#455A64', size=8),
               K.points3([[0, 1, 0]], name='qubit B (target)', color='#2E7D32', size=8),
               K.points3([[0, 0, 1]], name='bus mode', color='#B5530F', size=8)]
    path = lambda tr: [[x, z, y] for _, x, y, z in tr]
    fixed = [shell, dark] + corners
    for (name, T, e, tr), col in zip(pulses[:2], (COL_MIN, COL_SEQ)):
        fixed.append(K.curve3(path(tr), name='%s, %.0f ns: 1 − F_B = %.1f × 10⁻⁴' % (name, 1000 * T, e * E4),
                              color=col, width=3))
    frames, labels = [], []
    for (name, T, e, tr), col in zip(pulses[2:], COL_AD):
        end = tr[-1]
        frames.append([K.curve3(path(tr), name='%s (%.0f ns): 1 − F_B = %.1f × 10⁻⁴' % (name, 1000 * T, e * E4),
                                        color=col, width=4),
                               K.points3([[end[1], end[3], end[2]]], name='where it ends',
                                         color=col, size=9, star=True)])
        labels.append('%.0f ns' % (1000 * T))
    out = K.three_d(fixed, title='④ The path in 3D: A and B on the floor, the bus upwards (height = bus amplitude)',
                    axes=('|a| (qubit A)', '|b| (qubit B)', '|c| (bus)'),
                    slider={'label': 'duration of the adiabatic pulse', 'values': labels, 'items': frames})
    out['max_width'] = 900          # large in the full-screen right column
    return out


def _surface(ga, gb, qa, bus, qb, tg, meas, floor_v, t_star, emin, tmin):
    """3D: log10 of the bound L(T) over (T in ns, g/2π in MHz, the same ratio g_B/g_A), the valley (the floor for each
    coupling) and the reader's points."""
    ratio = gb / ga
    gs = [ga * 0.4 * (2.5 / 0.4) ** (k / 9) for k in range(10)]
    tmax = max(4 * t_star, 1.2 * (tg or 0) / 1000, 3 * tmin)
    ts = [tmin * 0.25 * (tmax / (0.25 * tmin)) ** (k / 17) for k in range(18)]
    grid, valley = [], []
    for g in gs:
        bound, _ = RF.link_bound(qa, bus, qb, g, g * ratio)
        grid.append([[1000 * t, g, math.log10(max(bound(t), 1e-12))] for t in ts])
        v, tt = RF.floor(qa, bus, qb, g, g * ratio, grid=60)
        valley.append([1000 * tt, g, math.log10(v)])
    items = [{'type': 'surface', 'grid': grid, 'name': 'bound on 1 − F_B for every pulse of duration T',
              'color': '#9ec3dc', 'opacity': 0.55},
             K.curve3(valley, name='the floor for each coupling (valley)', color='#1B6F8C', width=4),
             K.points3([[1000 * tmin, ga, math.log10(emin)]], name='minimal-time pulse (Lindblad)', color='#2E7D32',
                       size=7)]
    if meas is not None and tg is not None:
        items.append(K.points3([[tg, ga, math.log10(meas / E4)]], name='your measured error', color='#B00020',
                               size=9, star=True))
    return K.three_d(items, title='The bound as a surface: duration × coupling (log₁₀ of 1 − F_B)',
                     axes=('T (ns)', 'g/2π (MHz)', 'log₁₀(1 − F_B)'))


def run_link(params):
    try:
        ga, gb, qa, bus, qb, meas, tg = _read(params)
    except (TypeError, ValueError):
        return K.error('every field is a number (the measured error, the duration and g_B may be left blank)')
    msg = _check(ga, gb, qa, bus, qb, meas, tg)
    if msg:
        return K.error(msg)
    sigma, ut, ug = _unc(params)
    pm = json.loads(params) if isinstance(params, str) else params
    metric = str(pm.get('metric', 'average') or 'average')
    if metric not in ('average', 'process', 'efficiency'):
        return K.error('metric: average, process or efficiency')
    if metric == 'process' and meas is not None:        # 1 − F_avg = (2/3)(1 − F_e) for a qubit channel
        meas, sigma = meas * 2 / 3, sigma * 2 / 3
    if not (0 <= sigma < 1e4 and 0 <= ut < 90 and 0 <= ug < 90):
        return K.error('uncertainties: σ ≥ 0 (× 10⁻⁴); ± % on times and couplings between 0 and 90')
    floor_v, t_star = RF.floor(qa, bus, qb, ga, gb)
    bound_nom, _ = RF.link_bound(qa, bus, qb, ga, gb)
    L_tg = bound_nom(tg / 1000) if tg is not None else None

    def ref_at(sign):                      # the bound used for the verdict, at the corner of the uncertainties
        a, c, b, x, y = _corner(qa, bus, qb, ga, gb, ut, ug, sign)
        if tg is not None:
            return RF.link_bound(a, c, b, x, y)[0](tg / 1000)
        return RF.floor(a, c, b, x, y)[0]
    ref_lo, ref_hi = (ref_at(+1), ref_at(-1)) if (ut or ug) else ((L_tg, L_tg) if tg is not None else (floor_v, floor_v))
    if metric == 'efficiency':                         # the measured number is 1 − P: compare with the floor of 1 − P
        def pfloor(a, c, b, x, y, at=None):
            G = 2 * math.pi * min(x, y)
            pp = [RF.Problem(1 / e[0], 1 / c[0], 1 / r[0], 2 * math.pi * ge, 2 * math.pi * gr)
                  for (e, ge), (r, gr) in (((a, x), (b, y)), ((b, y), (a, x)))]
            f = lambda T: 1 - min(q.amplitude(T) for q in pp) ** 2
            if at is not None:
                return f(at)
            ts = [0.05 / G * (8000 ** (k / 200)) for k in range(201)]
            return min(f(t) for t in ts)
        floor_v = pfloor(qa, bus, qb, ga, gb)
        L_tg = pfloor(qa, bus, qb, ga, gb, tg / 1000) if tg is not None else None
        def pref(sign):
            a, c, b, x, y = _corner(qa, bus, qb, ga, gb, ut, ug, sign)
            return pfloor(a, c, b, x, y, tg / 1000 if tg is not None else None)
        ref_lo, ref_hi = (pref(+1), pref(-1)) if (ut or ug) else ((L_tg, L_tg) if tg is not None else (floor_v, floor_v))
    rel = lambda e: (e[0], 2 * e[0])
    relax_v, _ = RF.floor(rel(qa), rel(bus), rel(qb), ga, gb)
    gmin = min(ga, gb)
    emin, tmin = RL.minimal_time_error(qa, bus, qb, gmin)
    design = _design(ga, gb, qa, bus, qb)

    t = []
    t.append('FLOOR. No pulse, of any shape, phase or duration, with couplings up to %s MHz%s and these coherence '
             'times, can bring 1 − F_B below %s × 10⁻⁴ (Proposition 7.2 with the term f_A(T)², and reciprocity, '
             'Proposition 7.3). The bound is smallest for pulses of about %s ns; that duration minimises the bound, '
             'it is not the duration of the best pulse. This holds for one effective bus mode and Markovian dephasing '
             'at the given T2.'
             % (_f(ga), '' if gb == ga else ' (A) and %s MHz (B)' % _f(gb), _f(floor_v * E4), _f(1000 * t_star, 1)))
    share = 100 * (1 - relax_v / floor_v) if floor_v > 0 else 0
    t.append('RELAXATION ONLY. With T2 = 2 T1 everywhere (no pure dephasing) the floor would be %s × 10⁻⁴, so pure '
             'dephasing accounts for %s %% of the floor (a difference of two bounds, not a decomposition of a measured '
             'error).' % (_f(relax_v * E4), _f(share, 0)))
    t.append('ROBUST FLOOR. The relaxation-only floor, %s × 10⁻⁴, holds for ANY dephasing noise, Markovian or not '
             '(slow noise, 1/f, a random static detuning): it uses only the loss rates 1/T1, and for every noise '
             'realisation the populations obey the same inequalities, while the coherence never exceeds the square '
             'root of the population (Jensen). The full floor, %s × 10⁻⁴, assumes Markovian dephasing at the given T2.'
             % (_f(relax_v * E4), _f(floor_v * E4)))
    if tg is not None:
        t.append('AT YOUR DURATION. For pulses of exactly %s ns the bound is %s × 10⁻⁴ (the floor %s × 10⁻⁴ is its '
                 'minimum over all durations). A pulse of your duration cannot do better than this; to reach the floor '
                 'the duration would have to change too.' % (_f(tg, 0), _f(L_tg * E4), _f(floor_v * E4)))
    t.append('A SIMPLE PULSE. The simultaneous pulse g_A = g_B = %s MHz for π/(√2 G) = %s ns, the fastest complete '
             'transfer with one mode, gives 1 − F_B = %s × 10⁻⁴ in the Lindblad master equation with the same times: '
             '%s × the floor. Between this pulse and the floor lies what pulse shaping can still gain.'
             % (_f(gmin), _f(1000 * tmin, 1), _f(emin * E4), _f(emin / floor_v)))
    if meas is not None:
        r = meas / E4 / floor_v
        if r < 1:
            t.append('VERDICT: YOUR MEASURED ERROR (%s × 10⁻⁴) IS BELOW THE FLOOR (%s × 10⁻⁴). Within the model this '
                     'is impossible, so one of its hypotheses does not hold for your link. %s'
                     % (_f(meas), _f(floor_v * E4), _hypotheses()))
        else:
            v = ('VERDICT: your measured error is %s × the floor. Within the model, a better pulse could lower it by '
                 'at most this factor; the hardware sets the rest.' % _f(r, 1))
            if meas / E4 > emin:
                v += (' The minimal-time pulse would already give %s × less than your measurement, if its hypotheses '
                      '(one mode, Markovian dephasing, these times at full coupling) hold.' % _f(meas / E4 / emin, 1))
            else:
                v += ' Your pulse already beats the simple minimal-time pulse.'
            if r < 1.5:
                v += ' You are close to the floor: to go lower, change the hardware (see the bars).'
            t.append(v)
    if tg is not None:
        if tg < 1000 * tmin * (1 - 1e-9):
            t.append('DURATION: %s ns is below the single-mode minimal time %s ns at this coupling: impossible with '
                     'one mode and couplings up to %s MHz (Isabelle, relay_minimal_time). Check the coupling or the '
                     'number of modes.' % (_f(tg, 0), _f(1000 * tmin, 1), _f(gmin)))
        else:
            t.append('DURATION: your pulse lasts %s × the minimal time.' % _f(tg / (1000 * tmin), 1))
    pulses = _pulses(gmin, qa, bus, qb, tmin)
    ad = pulses[2:]
    t.append('THE RELAY SPHERE (3D). The point (|a|, |b|, |c|) follows the excitation: A and B on the floor, the bus '
             'upwards; the height is the amplitude in the bus. '
             'The minimal-time pulse climbs into the bus (%s × 10⁻⁴); two sequential swaps go through the bus corner '
             '(%s × 10⁻⁴); adiabatic pulses hug the dark-state path on the floor, more closely the longer they last, '
             'but the qubits decay meanwhile: %s × 10⁻⁴ for durations %s ns. Move the slider: this is the trade-off '
             'that the floor (%s × 10⁻⁴) makes rigorous for every pulse.'
             % (_f(pulses[0][2] * E4), _f(pulses[1][2] * E4), ', '.join(_f(p[2] * E4) for p in ad),
                ', '.join('%.0f' % (1000 * p[1]) for p in ad), _f(floor_v * E4)))
    if ad[0][2] > 5 * ad[1][2]:
        t[-1] += (' The shortest adiabatic pulse is too fast to follow the dark state: the excitation is left behind '
                  '(its end point stays far from B).')
    best_ad = min(ad, key=lambda p: p[2])
    t[-1] += (' Among the adiabatic pulses the best is the one of %.0f ns (%s × 10⁻⁴): shorter ones are not adiabatic, '
              'longer ones lose to qubit decay.' % (1000 * best_ad[1], _f(best_ad[2] * E4)))
    best = design[0]
    t.append('DESIGN. Of the changes in the bars, «%s» lowers the floor most: to %s × 10⁻⁴ (−%s %%). These are changes '
             'of the floor, not of the error of a particular pulse, and each keeps the other times fixed.'
             % (best[0], _f(best[1] * E4), _f(100 * (1 - best[1] / floor_v), 0)))

    # the figures go in pairs and share one colour per pulse (Carles, 31-oct: «dos fig, una describe una cosa y la
    # otra otra, pero que se vea que van unidas»): (1) how much error, (2) why: where each pulse keeps the excitation
    names = ['minimal time', 'sequential swaps'] + ['adiabatic %g×' % f for f in (2, 4, 8, 16)]
    cols = [COL_MIN, COL_SEQ] + COL_AD
    bound, _ = RF.link_bound(qa, bus, qb, ga, gb)
    tmax = max(1.3 * max(p[1] for p in pulses), 1.25 * (tg or 0) / 1000)
    ts = [t_star * 0.15 * (tmax / (0.15 * t_star)) ** (k / 70) for k in range(71)]
    ys = [max(bound(x), 1e-12) * E4 for x in ts]
    series = [{'name': 'below the bound: no pulse of that duration gets there', 'x': [1000 * x for x in ts],
               'y': ys, 'mode': 'area', 'color': '#7FA7C2'},
              {'name': 'floor %s × 10⁻⁴: no pulse of any duration gets below' % _f(floor_v * E4),
               'x': [1000 * ts[0], 1000 * ts[-1]], 'y': [floor_v * E4] * 2, 'mode': 'line', 'color': '#6A1B9A'},
              {'name': 'adiabatic pulses (one family, longer and longer)', 'x': [1000 * p[1] for p in ad],
               'y': [p[2] * E4 for p in ad], 'mode': 'line', 'color': COL_AD[2]}]
    where = ['left', 'above', 'above', 'below', 'below', 'left']
    for (name, T, e, _), lab, c, w in zip(pulses, names, cols, where):
        series.append({'x': [1000 * T], 'y': [e * E4], 'mode': 'points', 'color': c, 'size': 6, 'labels': [lab],
                       'label_pos': [w]})
    if meas is not None and tg is not None:
        series.append({'name': 'your measured error', 'x': [tg], 'y': [meas], 'mode': 'points', 'color': COL_MEAS,
                       'size': 7, 'labels': ['you'], 'label_pos': ['left']})
    how_much = K.svg_plot(series, title='① How much error: each pulse against the floor',
                          xlabel='pulse duration (ns, log scale)', ylabel='1 − F_B (× 10⁻⁴, log scale)', logy=True,
                          logx=True)
    occ = []
    for (name, T, e, tr), lab, c in zip(pulses, names, cols):
        o = [0.0, 0.0, 0.0]
        for (t0, *u0), (t1, *u1) in zip(tr[:-1], tr[1:]):
            for j in range(3):
                o[j] += 0.5 * (u0[j] ** 2 + u1[j] ** 2) * (t1 - t0) * 1000
        occ.append((lab, c, o))
    # ② where the error comes from, in the language of the experiments: IBM's additive budget (time in each element
    # × (1/3T1 + 1/3Tφ), Ref. [IBM]) on the occupations of each pulse, split by source; the Lindblad total beside it
    phi = lambda e: max(1 / e[1] - 1 / (2 * e[0]), 0.0)
    budget, budget_abs = [], []
    for (name, T, e, _), (lab, c, o) in zip(pulses, occ):
        tA, tC, tB = (x / 1000 for x in o)                  # µs
        parts = [tA / (3 * qa[0]) + tB / (3 * qb[0]), tA * phi(qa) / 3 + tB * phi(qb) / 3,
                 tC / (3 * bus[0]), tC * phi(bus) / 3]
        first = sum(parts)
        rest = max(e - first, 0.0)               # what the first-order budget does not see (non-adiabatic, ...)
        tot = max(e, first) or 1.0
        note = '%s × 10⁻⁴' % _f(e * E4, 1) + ('' if first <= e * 1.05 else ' (1st order %s)' % _f(first * E4, 1))
        budget.append((lab, c, [100 * x / tot for x in parts + [rest]], note))
        budget_abs.append(parts)
    why = K.stacked_bars(budget, [('qubit relaxation', '#B0BEC5'), ('qubit dephasing', '#546E7A'),
                                  ('bus relaxation', '#FFCC80'), ('bus dephasing', '#EF6C00'),
                                  ('beyond first order (e.g. not adiabatic)', '#D81B60')],
                         title='② Where the error comes from (same pulses, same colours as ①)',
                         xlabel='share of each pulse’s error (%): time in each element × (1/3T1 + 1/3Tφ), '
                                'the rest from Lindblad')
    # ③ what happens during the pulse: populations of A, the bus and B against time (as in the experiments' figures)
    best_i = 2 + min(range(len(ad)), key=lambda i: ad[i][2])
    pops = []
    for i, tag in ((0, 'minimal time'), (1, 'sequential swaps'), (best_i, 'best adiabatic')):
        name, T, e, tr = pulses[i]
        tt = [1000 * x[0] for x in tr]
        pops.append(K.svg_plot([{'name': 'qubit A', 'x': tt, 'y': [x[1] ** 2 for x in tr], 'mode': 'line', 'color': '#78909C'},
                                {'name': 'bus', 'x': tt, 'y': [x[2] ** 2 for x in tr], 'mode': 'line', 'color': '#EF6C00'},
                                {'name': 'qubit B', 'x': tt, 'y': [x[3] ** 2 for x in tr], 'mode': 'line', 'color': '#43A047'}],
                               title='%s, %.0f ns: %s × 10⁻⁴' % (tag, 1000 * T, _f(e * E4, 1)),
                               xlabel='time (ns)', ylabel='population', width=380, height=240))
    pops = [K.row(pops)]
    pops[0]['title'] = '③ During the pulse: populations of qubit A, the bus and qubit B'
    b0, bb = budget_abs[0], budget_abs[best_i]
    t.append('THE FIGURES. ① puts every pulse against the floor. ② says where each error comes from, with the '
             'first-order budget that IBM uses (time in each element × (1/3T1 + 1/3Tφ)), next to the exact Lindblad '
             'value: for the minimal-time pulse %s × 10⁻⁴ from the qubits and %s from the bus; for the best adiabatic '
             'pulse %s and %s. Fast pulses pay the bus, slow ones the qubits; Theorems 4.1 and 5.2 turn exactly these '
             'two occupations into the floor. ③ shows the populations during three of the pulses, the figure the '
             'experiments draw.'
             % (_f(b0[0] + b0[1], 1), _f(b0[2] + b0[3], 1), _f(bb[0] + bb[1], 1), _f(bb[2] + bb[3], 1)))
    barras = K.bars([(lab, v * E4, '#2E7D32' if i == 0 else None) for i, (lab, v) in enumerate(design)],
                    title='⑤ Which hardware change lowers the floor most', xlabel='floor on 1 − F_B (× 10⁻⁴)',
                    ref=floor_v * E4, ref_label='now %s' % _f(floor_v * E4))
    sphere = _sphere(pulses, floor_v)
    rows = [['floor, every pulse', _f(floor_v * E4), 'Props. 7.2–7.3'],
            ['floor, relaxation only', _f(relax_v * E4), 'T2 = 2T1 everywhere']]
    if meas is not None:
        rows.append(['your measured error', _f(meas), '%s × the floor' % _f(meas / E4 / floor_v, 1)])
    for (name, T, e, _), o in zip(pulses, occ):
        rows.append([name, _f(e * E4), 'Lindblad, %.0f ns; bus %.1f ns, qubits %.1f ns' % (1000 * T, o[2][1],
                                                                                          o[2][0] + o[2][2])])
    t.insert(0, {'average': 'METRIC: average fidelity of the channel at B, 1 − F_B (what network benchmarking estimates).',
                 'process': 'METRIC: you entered a process infidelity 1 − F_e; it is converted to 1 − F_avg = (2/3)(1 − F_e) '
                            'for a qubit channel (not valid with leakage or post-selection).',
                 'efficiency': 'METRIC: you entered a transfer loss 1 − P (efficiency). The verdict compares it with the '
                               'floor of 1 − P (Proposition 7.2 at the rates 1/T1); the figures stay in 1 − F_B.'}[metric])
    return K.result(_card(floor_v, relax_v, meas, sigma, tg, L_tg, ref_lo, ref_hi, (ut, ug), pulses, names, design,
                          'on 1 − P' if metric == 'efficiency' else 'on 1 − F_B')
                    + '<details class="lm-why"><summary>How to read '
                    'it: the floor, the pulses, the verdict, the hypotheses</summary>' +
                    ''.join('<p>%s</p>' % x for x in t) + '</details>', [how_much, why] + pops + [sphere, barras],
                    K.table(['quantity', '1 − F_B (× 10⁻⁴)', 'note'], rows))


def _card(floor_v, relax_v, meas, sigma, tg, L_tg, ref_lo, ref_hi, unc, pulses, names, design, on='on 1 − F_B'):
    """The result card: three numbers and a one-line verdict in colour; the reasoning stays folded below."""
    box = ('<div style="flex:1;min-width:120px;background:#f6f9fb;border:1px solid #dde6ee;border-radius:8px;'
           'padding:.45em .6em;text-align:center"><div style="font:12px Arial,sans-serif;color:#556">%s</div>'
           '<div style="font:bold 22px Arial,sans-serif;color:%s">%s</div><div style="font:11px Arial,sans-serif;'
           'color:#778">%s</div></div>')
    best_i = min(range(len(pulses)), key=lambda i: pulses[i][2])
    nums = [box % ('floor, any pulse and duration', '#6A1B9A', _f(floor_v * E4), '× 10⁻⁴ ' + on)]
    if L_tg is not None:
        nums.append(box % ('bound at your duration', '#4527A0', _f(L_tg * E4), '%.0f ns' % tg))
    nums.append(box % ('best simple pulse', '#1B6F8C', _f(pulses[best_i][2] * E4), names[best_i]))
    where = 'at your duration' if L_tg is not None else 'over all durations'
    ref = L_tg if L_tg is not None else floor_v
    if meas is not None:
        nums.append(box % ('your measured error', '#111', _f(meas) + ('' if not sigma else ' ± ' + _f(sigma, 1)),
                           '%s × the bound %s' % (_f(meas / E4 / ref, 1), where)))
        hi_m, lo_m = (meas + sigma) / E4, (meas - sigma) / E4
        if hi_m < ref_lo:
            col, msg = '#C62828', ('Incompatible with the model as declared: even the most favourable corner of your '
                                   'uncertainties puts the bound %s above your measurement. One of the hypotheses, '
                                   'the calibration or the metric does not hold for this link (open «How to read it»).'
                                   % where)
        elif lo_m < ref_hi:
            col, msg = '#EF6C00', ('Inconclusive: within the uncertainties your measurement may touch the bound %s. '
                                   'Narrow the uncertainties, or check the hypotheses.' % where)
        else:
            col, msg = '#2E7D32', ('No contradiction with the model. A pulse of your duration could lower the error by '
                                   'at most %s ×; with any duration, by at most %s × (bounds, not promises).'
                                   % (_f(meas / E4 / ref, 1), _f(meas / E4 / floor_v, 1)))
    else:
        col, msg = '#1B6F8C', 'Enter your measured error (and its ± σ) to get a verdict.'
    lever = design[0]
    return ('<div class="lm-card" style="font:13px/1.45 Arial,sans-serif">'
            '<div style="display:flex;gap:.5em;flex-wrap:wrap">%s</div>'
            '<div style="margin:.55em 0;padding:.45em .7em;border-radius:6px;color:#fff;background:%s;font-weight:bold">'
            '%s</div><div style="color:#334">Robust floor, any dephasing noise (Markovian or not): <b>%s</b> × 10⁻⁴. '
            'Biggest hardware lever: <b>%s</b> → floor %s × 10⁻⁴ (−%s %%).%s</div></div>'
            % (''.join(nums), col, msg, _f(relax_v * E4), lever[0], _f(lever[1] * E4),
               _f(100 * (1 - lever[1] / floor_v), 0),
               '' if not (unc[0] or unc[1]) else ' Uncertainties: times ± %g %%, couplings ± %g %%.' % unc))


def random_link():
    """The dice: a plausible link (every input changes; T2 ≤ 2 T1; duration ≥ the minimal time; measured error, when
    given, at least the floor)."""
    ga = random.uniform(2, 25)
    gb = '' if random.random() < 0.6 else '%.2f' % (ga * random.uniform(0.6, 1.6))
    e = []
    for lo, hi in ((20, 300), (5, 100), (20, 300)):
        t1 = random.uniform(lo, hi)
        e.append((t1, random.uniform(0.05, 2.0) * t1))
    gmin = min(ga, float(gb) if gb else ga)
    tmin = 1000 / (2 * math.sqrt(2) * gmin)
    tg = random.uniform(1.0, 9.0) * tmin
    fl = RF.floor(e[0], e[1], e[2], ga, float(gb) if gb else ga, grid=50)[0]
    meas = '' if random.random() < 0.25 else '%.2f' % (fl * E4 * random.uniform(1.05, 20))
    sig = '' if not meas else '%.1f' % (float(meas) * random.uniform(0.02, 0.15))
    met = random.choice(['average', 'average', 'process', 'efficiency'])
    return json.dumps({'metric': met, 'sigma': sig, 'unc_t': '%.0f' % random.uniform(0, 25), 'unc_g': '%.0f' % random.uniform(0, 10),
                       'ga_mhz': '%.2f' % ga, 'gb_mhz': gb, 't1a': '%.1f' % e[0][0], 't2a': '%.1f' % e[0][1],
                       't1c': '%.1f' % e[1][0], 't2c': '%.1f' % e[1][1], 't1b': '%.1f' % e[2][0],
                       't2b': '%.1f' % e[2][1], 'measured': meas, 'tg_ns': '%.0f' % tg})
