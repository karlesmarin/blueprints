# encaje: laboratorio del blueprint qsl-diagnostics para la Sección VIII (transferencia entre chips; versión 2);
# Python puro (Pyodide); la ecuación maestra es la de relevo/lindblad_rk4.py del paquete (comprobada en prueba_labs.py).
"""run_relay: the diagnostic of Section VIII on the reader's own link.

Single-excitation relay A -> cable mode C -> B, couplings |g1|, |g2| <= g (g/2pi in MHz). Prints the certified floor
pi/(2 sqrt2 g) (Lean, Gate.fsAngle_le_time_halfWidth), the single-mode minimal time pi/(sqrt2 g) (Boscain et al.;
lower half machine-checked in Isabelle, Relay_Minimal_Time.relay_minimal_time), the sequential time pi/g, the ratios
of the reader's duration, IBM's additive coherence model at that duration (occupations 1/2, 1/2) and, by the Lindblad
master equation (relaxation + Markovian pure dephasing, average fidelity over the channel with leakage), the coherence
error of the constant-coupling protocol stretched to each duration T >= T_min (couplings pi/(sqrt2 T)). The curve is
the error of ONE family of protocols, not a floor: slower protocols of other shapes can lose less.
"""
import json
import math
import random

import labkit as K

DOS_PI = 2 * math.pi


def _ec1(t, t1, t2):
    """IBM Eq. (1): error of one element holding the excitation for a time t (all in µs)."""
    return 0.5 * (1 - (math.exp(-t / t1) + 2 * math.exp(-t / t2)) / 3)


def _deriv(r, g, k1, gp):
    """dρ/dt for the 4x4 density matrix (0 vacuum, 1 A, 2 C, 3 B), H = g(|A><C| + |C><B| + h.c.)."""
    n = 4
    H = [[0.0] * n for _ in range(n)]
    H[1][2] = H[2][1] = H[2][3] = H[3][2] = g
    d = [[0j] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            s = 0j
            for c in range(n):
                s += H[a][c] * r[c][b] - r[a][c] * H[c][b]
            d[a][b] = -1j * s
    for j in (1, 2, 3):
        k = k1[j]
        d[0][0] += k * r[j][j]
        for a in range(n):
            if a != j:
                d[j][a] -= 0.5 * k * r[j][a] + gp[j] * r[j][a]
                d[a][j] -= 0.5 * k * r[a][j] + gp[j] * r[a][j]
        d[j][j] -= k * r[j][j]
    return d


def _rk4(r, g, k1, gp, T, steps):
    h = T / steps
    ad = lambda x, y, c: [[x[i][j] + c * y[i][j] for j in range(4)] for i in range(4)]
    for _ in range(steps):
        a = _deriv(r, g, k1, gp)
        b = _deriv(ad(r, a, h / 2), g, k1, gp)
        c = _deriv(ad(r, b, h / 2), g, k1, gp)
        e = _deriv(ad(r, c, h), g, k1, gp)
        r = [[r[i][j] + h / 6 * (a[i][j] + 2 * b[i][j] + 2 * c[i][j] + e[i][j]) for j in range(4)] for i in range(4)]
    return r


def lindblad_error(T, t1q, t2q, t1c, t2c, steps=None):
    """Coherence error (fraction) of the constant-coupling protocol of duration T (µs), g = pi/(sqrt2 T)."""
    g = math.pi / (math.sqrt(2) * T)
    k1 = {1: 1 / t1q, 2: 1 / t1c, 3: 1 / t1q}
    gp = {1: 1 / t2q - 1 / (2 * t1q), 2: 1 / t2c - 1 / (2 * t1c), 3: 1 / t2q - 1 / (2 * t1q)}
    # 30-oct: 400 steps blocked the browser (Pyodide); 100 steps give a relative error ≤ 1.5e-6, 40 steps ≤ 1.5e-4
    # (measured against 800 steps at 39 ns, 312 ns and 1 µs)
    steps = steps or 100
    out = {}
    for (i, k) in ((0, 0), (0, 1), (1, 1)):
        r = [[0j] * 4 for _ in range(4)]
        r[0 if i == 0 else 1][0 if k == 0 else 1] = 1
        o = _rk4(r, g, k1, gp, T, steps)
        out[(i, k)] = [[o[0][0], o[0][3]], [o[3][0], o[3][3]]]
    z = (1, -1)                                   # the optimal protocol puts a phase -1 on |B>
    fe = sum(((z[i] * z[k]) * out[(i, k)][i][k]).real for (i, k) in ((0, 0), (1, 1))) / 4
    fe += 2 * ((z[0] * z[1]) * out[(0, 1)][0][1]).real / 4
    tr = (out[(0, 0)][0][0] + out[(0, 0)][1][1] + out[(1, 1)][0][0] + out[(1, 1)][1][1]).real
    return 1 - (2 * fe + tr / 2) / 3


IBM_LINKS = [('Q240–Q247', 121.0, 14.0, 28.8, 36.0, 0.71), ('Q241–Q246', 99.7, 7.1, 38.6, 51.0, 1.13),
             ('Q242–Q245', 146.3, 11.0, 22.7, 37.0, 1.01), ('Q243–Q244', 112.0, 7.7, 24.8, 37.0, 1.14)]


def first_order_error(g_mhz, t1q, t2q, t1c, t2c):
    """Coherence error (fraction) of the constant-coupling protocol at the minimal time, to first order: identity R1,
    1 − F = T_min [γ1q/4 + γ1c/12 + (37/96) γφq + (3/16) γφc], T_min = π/(√2 g) (0.12905 % against the master
    equation's 0.1289 % on Q240–Q247). Closed form, so a whole surface costs nothing."""
    t = 1 / (2 * math.sqrt(2) * g_mhz)               # µs
    gpq, gpc = 1 / t2q - 1 / (2 * t1q), 1 / t2c - 1 / (2 * t1c)
    return t * (1 / (4 * t1q) + 1 / (12 * t1c) + 37 / 96 * gpq + 3 / 16 * gpc)


def _three_d(g_mhz, tg, t1q, t2q, t1c, t2c, lb_min, meas):
    """The landscape an engineer reads at a glance (Carles 30-oct: «una imagen 3D más clara, que sea intuitiva»).
    Axes: what you control, coupling g/2π and duration T, and the error. The red WALL at T = π/(√2 g) is the speed
    limit: nothing gets behind it. The RAMP in front of it is the coherence error of the constant-coupling protocol,
    which to first order is T times a coherence constant (identity R1), so it rises with the duration and does not
    depend on g. Your link is a star at (g, T_g, measured error), dropped onto the ramp; the arrow slides down the ramp to
    the wall: what speed alone can buy. IBM's four links in orange. Slider: qubit coherence (T2* × 0.5 … × 4)."""
    gmax = max(30.0, 1.3 * g_mhz)
    tmax = max(1.3 * tg, 3000 / (2 * math.sqrt(2) * 2))          # ns: past your T_g and the wall at 2 MHz
    gs = [1 + (gmax - 1) * k / 14 for k in range(15)]
    wall = lambda g: 1000 / (2 * math.sqrt(2) * g)               # ns
    # the viewer draws the three axes on ONE scale (lab3d.js): T (hundreds of ns) and the error (≈ 1 %) are shown in
    # round units chosen so that each axis spans about as much as the coupling axis (30 MHz); the unit is in the label
    nice = lambda v: min((m * 10 ** e for e in range(-6, 7) for m in (1, 2, 5) if m * 10 ** e >= v), default=v)
    uT = nice(tmax / gmax)
    frames, vals = [], []
    for fac in (0.5, 1.0, 2.0, 4.0):
        q2 = t2q * fac
        q1 = max(t1q, q2 / 2)                                    # T2* ≤ 2 T1 always
        slope = 100 * first_order_error(1.0, q1, q2, t1c, t2c) / wall(1.0)   # % per ns (the ramp is T times this)
        # ramp: for each g, from the wall to T_max (so the surface starts exactly at the wall)
        ramp = K.surface3(lambda g, s: [g, wall(g) + s * (tmax - wall(g)), slope * (wall(g) + s * (tmax - wall(g)))],
                          gs, [k / 10 for k in range(11)], 'coherence error of the fastest-shape protocol stretched '
                          'to T (qubit T2* × %g)' % fac, color='#9cc3e6', opacity=0.6)
        frames.append([ramp])
        vals.append('qubit T2* × %g' % fac)
    # the wall is as tall as the steepest ramp (qubit T2* × 0.5) at T_max, or your measured error if higher
    worst = 100 * first_order_error(1.0, max(t1q, t2q / 4), t2q / 2, t1c, t2c) / wall(1.0)
    ztop = max(worst * tmax, meas or 0)
    fixed = [K.surface3(lambda g, s: [g, wall(g), s * ztop], gs, [k / 4 for k in range(5)],
                        'the speed limit T = π/(√2 g): nothing gets behind this wall', color='#E05252', opacity=0.2)]
    s1 = 100 * first_order_error(1.0, t1q, t2q, t1c, t2c) / wall(1.0)
    on_ramp = [g_mhz, tg, s1 * tg]
    at_wall = [g_mhz, wall(g_mhz), s1 * wall(g_mhz)]
    fixed.append(K.points3([on_ramp], 'your link on the ramp (coherence only, at T_g)', color='#1B6F8C', size=7))
    fixed.append(K.curve3([on_ramp, at_wall], 'sliding down to the wall: what speed alone can buy', color='#1B6F8C',
                          width=4))
    fixed.append(K.points3([at_wall], 'your link at the speed limit', color='#1B6F8C', size=9, star=True))
    if meas is not None:
        top = [g_mhz, tg, meas]
        fixed.append(K.points3([top], 'your measured error', color='#B00020', size=7))
        fixed.append(K.curve3([top, on_ramp], 'not coherence: calibration, leakage, other modes', color='#B00020',
                              width=2, dash=True))
    pts = []
    for name, a1, a2, b1, b2, m, tgi in [l + (t,) for l, t in zip(IBM_LINKS, (312, 296, 256, 312))]:
        pts.append([8.5, tgi, m])
    fixed.append(K.points3(pts, 'IBM’s four links (measured error at their T_g)', color='#E07B00', size=6))
    # one place to rescale: every item was built in physical units (MHz, ns, %); the error axis is drawn at about
    # 0.6 of the coupling axis, so the ramp and the wall read as a landscape and not as a line
    uZ = nice(ztop / (0.6 * gmax))

    def esc(v):
        return [v[0], v[1] / uT, v[2] / uZ]

    def escalar(it):
        if it['type'] == 'surface':
            it['grid'] = [[esc(v) for v in row] for row in it['grid']]
        else:
            it['points'] = [esc(v) for v in it['points']]
        return it
    fixed = [escalar(it) for it in fixed]
    frames = [[escalar(it) for it in fr] for fr in frames]
    fmt = lambda u: ('%g' % u).replace('-', '−')
    return K.three_d(fixed, 'The speed-limit wall and the coherence ramp: where your link sits',
                     axes=('coupling g/2π (MHz)', 'duration T (× %s ns)' % fmt(uT), 'error (× %s %%)' % fmt(uZ)),
                     slider={'label': 'qubit coherence', 'values': vals, 'items': frames})


def _lectura(tg, t_min, t_seq, t1q, t2q, t1c, t2c, add_tg, lb_min, lb_tg, meas):
    """Reading in words that follows the inputs (Carles 30-oct: «que al cambiar los parámetros explique también los
    resultados»): which term dominates the coherence error, how much speed is left, what part of the measured error
    coherence explains, and what improving each resource would do."""
    tau = tg / 2000                                  # µs per element in IBM's model
    tphq, tphc = 1 / (1 / t2q - 1 / (2 * t1q)), 1 / (1 / t2c - 1 / (2 * t1c))
    parts = {'qubit relaxation (T1 of the qubits)': tau / (3 * t1q), 'qubit dephasing (T2 of the qubits)': tau / (3 * tphq),
             'cable relaxation (T1 of the mode)': tau / (3 * t1c), 'cable dephasing (T2 of the mode)': tau / (3 * tphc)}
    tot = sum(parts.values())
    orden = sorted(parts.items(), key=lambda kv: -kv[1])
    s = ['Reading. In IBM\'s model at your T_g, %s gives %.0f %% of the coherence error and %s %.0f %%; the other two '
         'together %.0f %%.' % (orden[0][0], 100 * orden[0][1] / tot, orden[1][0], 100 * orden[1][1] / tot,
                                100 * (orden[2][1] + orden[3][1]) / tot)]
    if tg < t_min:
        s.append('Your duration is shorter than one mode allows with these couplings: either the couplings are larger '
                 'than g, or the protocol uses several cable modes.')
    elif tg < 1.3 * t_min:
        s.append('Your transfer is already within 30 %% of the single-mode minimal time: little speed is left; the '
                 'error can only come down through coherence or calibration.')
    else:
        s.append('Running at the minimal time would cut the time each element holds the excitation by %.1f×; by the '
                 'master equation the coherence error of the constant-coupling protocol would go from %.3f %% (at '
                 'T_g) to %.3f %%.' % (tg / t_min, 100 * (lb_tg or 0), 100 * lb_min))
    if lb_tg is not None and add_tg > 0:
        r = lb_tg / add_tg
        s.append('At T_g the master equation gives %.2f× IBM\'s additive value: %s.' % (
            r, 'the additive model underestimates, because pure dephasing also destroys the coherence BETWEEN qubit '
               'and cable while the excitation is shared' if r > 1.05 else
            'the two agree here (relaxation dominates, where the additive model is exact at first order)'))
    if meas is not None:
        f = 100 * (100 * add_tg) / meas             # add_tg is a fraction, meas is in %
        s.append('Coherence (IBM\'s model) explains %.0f %% of your measured error; the remaining %.3f %% is not '
                 'coherence in that model (control, leakage, other modes, or dephasing while the excitation is '
                 'shared).' % (min(f, 100), max(meas - 100 * add_tg, 0)) if f < 100 else
                 'IBM\'s coherence model alone already exceeds your measured error: the coherence times are '
                 'pessimistic (shorter T of the pair, Ramsey T2) or the duration is not the time the excitation spends '
                 'in the elements.')
    best = orden[0][0].split(' (')[0]
    s.append('Doubling the time behind «%s» would remove about %.0f %% of the coherence error at T_g.' % (
        best, 50 * orden[0][1] / tot))
    # the 3D question: at the minimal time the error is ∝ 1/g, so doubling g halves it; compare with doubling T2*
    g_mhz = 1000 / (2 * math.sqrt(2) * t_min)
    e0 = first_order_error(g_mhz, t1q, t2q, t1c, t2c)
    e2 = first_order_error(g_mhz, max(t1q, t2q), 2 * t2q, t1c, t2c)
    s.append('At the minimal time (3D figure): doubling the coupling g halves the coherence error (it scales as 1/g); '
             'doubling the qubit T2* instead would lower it by %.0f %%, so %s.' % (
                 100 * (1 - e2 / e0), 'coupling is the better buy' if (1 - e2 / e0) < 0.5 else
                 'qubit coherence is the better buy'))
    return ' '.join(s)


def random_relay():
    """The dice: a plausible link (coupling, duration a few times the minimal time, coherence times, measured error);
    every input changes."""
    g_mhz = random.uniform(2, 20)
    t_min = 1000 / (2 * math.sqrt(2) * g_mhz)
    t1q, t1c = random.uniform(20, 200), random.uniform(3, 60)
    t2q, t2c = random.uniform(0.2, 1.2) * t1q, random.uniform(0.4, 1.6) * t1c
    t2q, t2c = min(t2q, 2 * t1q), min(t2c, 2 * t1c)
    tg = random.uniform(1.05, 9.0) * t_min          # feasible: never below the single-mode minimal time
    # feasible measured error (Carles 30-oct: «dentro de lo que se pueda hacer»): at least the coherence error at T_g
    # (master equation of the stretched protocol and IBM's model, whichever is larger), plus up to 80 % more
    coh = max(lindblad_error(tg / 1000, t1q, t2q, t1c, t2c, steps=40),
              _ec1(tg / 2000, t1q, t2q) + _ec1(tg / 2000, t1c, t2c))
    meas = '' if random.random() < 0.25 else '%.3f' % (100 * random.uniform(1.0, 1.8) * coh)
    return json.dumps({'g_mhz': '%.2f' % g_mhz, 'tg_ns': '%.0f' % tg, 't1q': '%.1f' % t1q, 't2q': '%.1f' % t2q,
                       't1c': '%.1f' % t1c, 't2c': '%.1f' % t2c, 'measured': meas})


def run_relay(params):
    params = json.loads(params) if isinstance(params, str) else params
    try:
        g_mhz = float(params.get('g_mhz', 9))
        tg = float(params.get('tg_ns', 312))
        t1q, t2q = float(params.get('t1q', 121.0)), float(params.get('t2q', 14.0))
        t1c, t2c = float(params.get('t1c', 28.8)), float(params.get('t2c', 36.0))
        meas = params.get('measured', '')
        meas = float(meas) if str(meas).strip() else None
    except (TypeError, ValueError):
        return K.error('all fields are numbers (the measured error may be left blank)')
    if not (0.1 <= g_mhz <= 200 and 1 <= tg <= 1e5 and 0.1 <= t1q <= 1e5 and 0.1 <= t1c <= 1e5):
        return K.error('out of range: g/2π in 0.1–200 MHz, T_g in 1–100000 ns, T1 in 0.1–100000 µs')
    if t2q > 2 * t1q or t2c > 2 * t1c:
        return K.error('T2 cannot exceed 2 T1 (pure dephasing would be negative)')
    g = DOS_PI * g_mhz * 1e-3                    # rad/ns
    t_floor, t_min, t_seq = math.pi / (2 * math.sqrt(2) * g), math.pi / (math.sqrt(2) * g), math.pi / g
    add_tg = _ec1(tg / 2000, t1q, t2q) + _ec1(tg / 2000, t1c, t2c)
    lb_min = lindblad_error(t_min / 1000, t1q, t2q, t1c, t2c)
    lb_tg = lindblad_error(tg / 1000, t1q, t2q, t1c, t2c) if tg >= t_min else None
    text = ('Certified floor π/(2√2 g) = %.1f ns (Lean) · single-mode minimal time π/(√2 g) = %.1f ns (lower half in '
            'Isabelle) · sequential π/g = %.1f ns.\nYour transfer: T_g = %.0f ns = %.2f × the minimal time, %.2f × '
            'sequential, %.1f × the floor.\nIBM additive coherence model at T_g (occupations ½, ½): %.3f %%. Master '
            'equation of the constant-coupling protocol: %.3f %% at the minimal time%s.'
            % (t_floor, t_min, t_seq, tg, tg / t_min, tg / t_seq, tg / t_floor, 100 * add_tg, 100 * lb_min,
               ('' if lb_tg is None else ', %.3f %% stretched to T_g' % (100 * lb_tg))))
    if tg < t_min:
        text += '\nT_g is BELOW the single-mode minimal time: impossible with one mode and |g| ≤ g (several modes or a larger g?).'
    if meas is not None:
        text += '\nYour measured error %.3f %% is %.1f × the master-equation error at the minimal time.' % (
            meas, meas / (100 * lb_min))
    text += '\n\n' + _lectura(tg, t_min, t_seq, t1q, t2q, t1c, t2c, add_tg, lb_min, lb_tg, meas)
    text += '\nThe curve is one family of protocols, not a floor: a slower protocol of another shape can lose less.'
    # the axis always reaches past the reader's T_g, so that T_g, g and every coherence time move the figure
    top = max(3 * t_min, 1.15 * tg)
    ts = [t_min + (top - t_min) * k / 14 for k in range(15)]
    ys = [100 * lindblad_error(t / 1000, t1q, t2q, t1c, t2c, steps=40) for t in ts]
    ya = [100 * (_ec1(t / 2000, t1q, t2q) + _ec1(t / 2000, t1c, t2c)) for t in ts]
    series = [{'name': 'master equation, constant couplings stretched to T', 'x': ts, 'y': ys, 'mode': 'line',
               'color': '#1B6F8C'},
              {'name': 'IBM additive model, occupations ½, ½', 'x': ts, 'y': ya, 'mode': 'line', 'color': '#C06000'},
              {'name': 'minimal time (master equation)', 'x': [t_min], 'y': [100 * lb_min], 'mode': 'points',
               'color': '#1B6F8C', 'size': 7}]
    if tg >= t_min:
        series.append({'name': 'your T_g (IBM model)', 'x': [tg], 'y': [100 * add_tg], 'mode': 'points',
                       'color': '#C06000', 'size': 7})
    if meas is not None:
        series.append({'name': 'your measured error', 'x': [tg], 'y': [meas], 'mode': 'points', 'color': '#B00020',
                       'size': 7})
    plot = K.svg_plot(series, title='Coherence error against the transfer duration', xlabel='T (ns)',
                      ylabel='error (%)')
    rows = [['certified floor (Lean)', '%.1f' % t_floor, '%.1f' % (tg / t_floor)],
            ['minimal time, one mode', '%.1f' % t_min, '%.2f' % (tg / t_min)],
            ['sequential (two swaps)', '%.1f' % t_seq, '%.2f' % (tg / t_seq)]]
    return K.result(text, [_three_d(g_mhz, tg, t1q, t2q, t1c, t2c, lb_min, meas), plot],
                    K.table(['reference', 'time (ns)', 'T_g / time'], rows))
