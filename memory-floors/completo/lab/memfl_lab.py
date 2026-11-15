# encaje: laboratorios del blueprint memory-floors (paper A, «Exact limits on writing a superconducting quantum memory»):
# una run_* por figura calculada del paper (2D en vivo que la sustituye + una 3D pensada para ella) y una para el ciclo sin
# reinicio. Python puro (Pyodide); usa labkit.py (dibujo) y memfl_core.py (numérica). Miré Lemmario y labweb de Excovery:
# son quienes los EJECUTAN y prueban (se usan abajo); la numérica de este paper no existe en ellos. No es herramienta nueva.
"""Seven labs, each with a turnable 3D figure thought for its own idea:

- run_pstar  (Fig. 1, Theorem 1): the smallest loss 1 - P* against the familiar estimate; 3D: the surface with your point.
- run_cloud  (Fig. 2, Theorem 2): random pulses never pass P_phi; 3D: population over (duration, mean |g|) under two planes.
- run_fixed  (Fig. 3, Corollary 8): B_p(T) against the plain resonant pulse; 3D: surface over (GT, Phi/G), slider on Phi.
- run_env    (Fig. 4, Corollary 10): p + 2c and its envelopes; 3D: the two gaps as a space curve with its projections.
- run_rutgers(Fig. 5, Table 3): measured and simulated errors against the limit 1 - P_phi; 3D: the limit over (mode, qubit times).
- run_surface(Fig. 6, Section 8): r_res over coupling and transmon times; 3D: the surface with a slider on the transmon times.
- run_cycle  (Prop. on the memory cycle): the cycle without reset, first order and exact two-pulse dynamics.
Everything is computed here; the parameters of the devices come from memfl_core (cited there). Checked by comprueba_lab.py."""
import json
import math
import random

import labkit as K
import memfl_core as C

PAL = K.PALETTE


# ------------------------------------------------------------------ helpers

def _num(p, name, default, lo, hi, label):
    try:
        v = float(str(p.get(name, default)).replace(',', '.'))
    except ValueError:
        raise ValueError('%s must be a number' % label)
    if not (lo <= v <= hi):
        raise ValueError('%s must be between %g and %g' % (label, lo, hi))
    return v


def _surf(grid, name, color, opacity, colorfn=None):
    """A surface from a ready grid of [x, y, z]; colorfn(x, y, z) -> hex colours each vertex (labkit.surface3 convention)."""
    out = {'type': 'surface', 'grid': grid, 'name': name, 'color': color, 'opacity': opacity}
    if colorfn:
        out['colors'] = [[colorfn(*p) for p in row] for row in grid]
    return out


def _geom(a, b, n):
    return [a * (b / a) ** (i / (n - 1)) for i in range(n)]


def _lin(a, b, n):
    return [a + (b - a) * i / (n - 1) for i in range(n)]


def _times(p):
    T1q = _num(p, 'T1q', 20, 0.01, 1e5, 'the qubit T1')
    T2q = _num(p, 'T2q', 4, 0.01, 1e5, 'the qubit T2')
    T1m = _num(p, 'T1m', 100, 0.01, 1e6, 'the mode T1')
    T2m = _num(p, 'T2m', 40, 0.01, 1e6, 'the mode T2')
    for T1, T2, w in ((T1q, T2q, 'qubit'), (T1m, T2m, 'mode')):
        if T2 > 2 * T1 * (1 + 1e-9):
            raise ValueError('the %s T2 cannot exceed 2·T1 (the pure dephasing would be negative)' % w)
    return T1q, T2q, T1m, T2m


# ------------------------------------------------------------------ Figure 1: Theorem 1

def run_pstar(params):
    p = json.loads(params)
    try:
        gq = _num(p, 'gq', 0.05, 1e-4, 5, 'γq/G')
        gm = _num(p, 'gm', 0.01, 1e-4, 5, 'γm/G')
    except ValueError as e:
        return K.error(str(e))
    P, ts, regime = C.p_star(1.0, gq, gm)
    loss, est = 1 - P, C.folk(1.0, gq, gm)
    # the ray with your ratio gq : gm, rates from 1e-3 G upwards
    m = max(gq, gm)
    s_lo, s_hi = min(1e-3 / m, 0.5), max(1 / m, 1.3)
    ss = _geom(s_lo, s_hi, 45)
    xs = [math.log10((gq + gm) * s) for s in ss]
    ex = [1 - C.p_star(1.0, gq * s, gm * s)[0] for s in ss]
    es = [C.folk(1.0, gq * s, gm * s) for s in ss]
    rat = [a / b for a, b in zip(ex, es)]
    xr = math.log10(gq + gm)
    # colour = exact / estimate (1 = the estimate is right; darker = the estimate overshoots), the same code in 2D and 3D
    rlo = 0.90
    colr = [K.scale(r, rlo, 1.0, 'sequential') for r in rat]
    plotA = K.svg_plot([{'name': '1 − P* (smallest loss of any pulse)', 'x': xs, 'y': ex, 'mode': 'line', 'color': PAL[0]},
                        {'name': 'estimate 1 − e^{−π(γq+γm)/4G}', 'x': xs, 'y': es, 'mode': 'line', 'color': PAL[1]},
                        {'name': 'dots coloured by exact / estimate', 'x': xs, 'y': ex, 'mode': 'points', 'size': 3.5,
                         'colors': colr},
                        {'name': 'your point', 'x': [xr, xr], 'y': [loss, est], 'mode': 'points', 'size': 5,
                         'color': PAL[4]}],
                       title='Theorem 1 along your ratio γq:γm', xlabel='log10 of (γq+γm)/G',
                       ylabel='loss (log scale)', figure='paperfig-1', logy=True)
    plotB = K.svg_plot([{'name': 'exact / estimate', 'x': xs, 'y': rat, 'mode': 'line', 'color': '#999999'},
                        {'name': 'same colour code as the surface', 'x': xs, 'y': rat, 'mode': 'points', 'size': 3.5,
                         'colors': colr},
                        {'name': 'your point', 'x': [xr], 'y': [loss / est], 'mode': 'points', 'size': 5, 'color': PAL[4]},
                        {'name': 'the estimate (ratio 1)', 'x': [xs[0], xs[-1]], 'y': [1, 1], 'mode': 'line',
                         'color': '#999999'}],
                       title='The ratio of the two (Figure 1, right panel)', xlabel='log10 of (γq+γm)/G', ylabel='ratio')
    lo = min(1e-3, gq / 1.5, gm / 1.5)
    hi = max(0.5, 1.2 * gq, 1.2 * gm)
    ax = _geom(lo, hi, 18)
    gridE = [[[math.log10(a), math.log10(b), math.log10(1 - C.p_star(1.0, a, b)[0])] for b in ax] for a in ax]
    gridF = [[[math.log10(a), math.log10(b), math.log10(C.folk(1.0, a, b))] for b in ax] for a in ax]
    ray = [[math.log10(gq * s), math.log10(gm * s), math.log10(1 - C.p_star(1.0, gq * s, gm * s)[0])] for s in ss
           if lo <= min(gq, gm) * s and max(gq, gm) * s <= hi]          # only the part of the ray over the surface
    ratio_at = lambda x, y, z: 10 ** z / C.folk(1.0, 10 ** x, 10 ** y)       # exact / estimate at the vertex
    items = [_surf(gridE, '1 − P* (exact), coloured by exact / estimate', '#1B6F8C', 0.8,
                   lambda x, y, z: K.scale(ratio_at(x, y, z), rlo, 1.0, 'sequential')),
             _surf(gridF, 'estimate (above it everywhere)', '#B5530F', 0.22),
             K.curve3(ray, 'your ratio γq:γm', color='#C62828', width=3),
             K.points3([[math.log10(gq), math.log10(gm), math.log10(loss)]], 'your point', color='#C62828', size=9,
                       star=True)]
    plot3 = K.three_d(items, 'The smallest loss over both rates (log–log–log); the orange sheet is the estimate',
                      axes=('log10 γq/G', 'log10 γm/G', 'log10 loss'),
                      colorbar=K.colorbar('exact / estimate (light = 0.90, dark = 1: the estimate is exact)', rlo, 1.0,
                                          'sequential'))
    text = ('γq = %g G, γm = %g G (%s). Stopping time Gt* = %.5f (Theorem 1). <b>P* = %.6f</b>, so no pulse of any shape '
            'can leave less than <b>1 − P* = %.6f</b> of the excitation behind. The familiar estimate 1 − e^{−π(γq+γm)/4G} '
            '= %.6f is %s the exact minimum (Eq. (4) says it is never below): exact/estimate = <b>%.4f</b>. The stopping '
            'rule is |a|/|b| = γm/(2G) = %.4f. Symmetry check: swapping the two rates gives P* = %.6f.'
            % (gq, gm, regime, ts, P, loss, est, 'above' if est >= loss else 'BELOW', loss / est, gm / 2,
               C.p_star(1.0, gm, gq)[0]))
    return K.result(text, [plot3, plotA, plotB])


# ------------------------------------------------------------------ Figure 2: Theorem 2 (the cloud)

def run_cloud(params):
    p = json.loads(params)
    try:
        T1q, T2q, T1m, T2m = _times(p)
        n = int(_num(p, 'n', 300, 10, 600, 'the number of pulses'))
        cap = _num(p, 'cap', 1.0, 0.5, 2.0, 'the coupling cap |g|max/G')
        seed = int(_num(p, 'seed', 7, 0, 10 ** 6, 'the seed'))
    except ValueError as e:
        return K.error(str(e))
    G = 1.0
    gq, gm, eq, em, fq, fm = C.rates(T1q, T2q, T1m, T2m)
    F = fq + fm
    Pphi, tphi, att = C.p_phi(G, gq, gm, F)
    Pst = C.p_star(G, gq, gm)[0]
    rng = random.Random(seed)
    t0 = math.pi / (2 * G)
    pts = []
    for _ in range(n):
        T = rng.uniform(0.3, 2.6) * t0
        e1, e2, e3 = rng.choice([0, 0.3, 1]), rng.choice([0, 0.2, 1]), rng.choice([0, 0.3, 1])
        mods = [min(cap * G * rng.uniform(0.3, 1) ** e1, cap * G) for _ in range(8)]
        phs = [rng.uniform(-math.pi, math.pi) * e2 for _ in range(8)]
        dets = [rng.gauss(0, G) * e3 for _ in range(8)]
        pts.append((T, C.pop_pulse(T, mods, phs, dets, gq, gm, F), sum(mods) / (8 * G)))
    best = max(pts, key=lambda a: a[1])
    above = sum(1 for a in pts if a[1] > Pphi + 1e-9)
    tmax = 4.1
    dt = tmax / 200
    pres = C.p_res_series(G, gq, gm, F, dt, 200)
    tt = [i * dt for i in range(201)]
    # colour = how close to the ceiling (p / P_phi, light to dark); red = above the ceiling (the theorem forbids it)
    pcol = [K.verdict(False) if a[1] > Pphi + 1e-9 else K.scale(a[1] / Pphi, 0.0, 1.0, 'sequential') for a in pts]
    series = [{'name': '%d random pulses (dark = near P_φ, red = above it)' % n, 'x': [a[0] for a in pts],
               'y': [a[1] for a in pts], 'mode': 'points', 'size': 3, 'colors': pcol},
              {'name': 'resonant pulse g = G', 'x': tt, 'y': pres, 'mode': 'line', 'color': PAL[0]},
              {'name': 'P_φ (Markovian dephasing)', 'x': [0, tmax], 'y': [Pphi, Pphi], 'mode': 'line', 'color': PAL[1]},
              {'name': 'P* (any dephasing)', 'x': [0, tmax], 'y': [Pst, Pst], 'mode': 'line', 'color': PAL[2]}]
    if abs(cap - 1) > 1e-9:
        pc = C.p_res_series(cap * G, gq, gm, F, dt, 200)
        series.append({'name': 'resonant pulse at |g| = %g G (outside the theorem)' % cap, 'x': tt, 'y': pc,
                       'mode': 'line', 'color': PAL[4]})
    plot2 = K.svg_plot(series, title='Theorem 2: no random pulse passes P_φ', xlabel='duration (units of 1/G)',
                       ylabel='transferred population p_b', figure='paperfig-2')
    # 3D: population over (duration, mean |g|/G), the two ceilings as planes, the resonant pulse as a curve at |g| = G
    gs = [0.0, cap]
    planeP = [[[0.0, g, Pphi], [tmax, g, Pphi]] for g in gs]
    planeS = [[[0.0, g, Pst], [tmax, g, Pst]] for g in gs]
    items = [K.points3([[a[0], a[2], a[1]] for a in pts], '%d random pulses' % n, color='#777777', size=3.2, opacity=0.9,
                       colors=pcol),
             _surf(planeP, 'P_φ (nothing above this plane)', '#D55E00', 0.35),
             _surf(planeS, 'P* (any dephasing)', '#009E73', 0.18),
             K.curve3([[t, 1.0, v] for t, v in zip(tt, pres)], 'resonant pulse (|g| = G)', color='#1B6F8C', width=3),
             K.points3([[best[0], best[2], best[1]]], 'the best random pulse', color='#C62828', size=9, star=True)]
    plot3 = K.three_d(items, 'Each pulse is a point: duration, mean |g|/G, population reached',
                      axes=('duration G·T', 'mean |g|/G', 'p_b'),
                      colorbar=K.colorbar('population / P_φ', stops=[['0', K.scale(0, 0, 1, 'sequential')],
                                                                    ['0.5', K.scale(0.5, 0, 1, 'sequential')],
                                                                    ['1 = the ceiling', K.scale(1, 0, 1, 'sequential')],
                                                                    ['above P_φ (forbidden)', K.verdict(False)]]))
    if abs(cap - 1) < 1e-9:
        verdict = ('%d of %d random pulses are above P_φ (Theorem 2 says none can be).' % (above, n))
    else:
        verdict = ('With |g| allowed up to %g G the premise of the theorem is broken: %d of %d random pulses are above '
                   'P_φ(G) and the resonant pulse at %g G passes it (red line).' % (cap, above, n, cap))
    text = ('Qubit T1 = %g, T2 = %g; mode T1 = %g, T2 = %g (G = 1): Γ = %.4f, pure dephasing Φ = %.4f. <b>P_φ = %.4f</b> '
            'at Gt = %.4f%s; P* (relaxation only, any dephasing) = %.4f. The best of %d random pulses reaches <b>%.4f</b> '
            '(%.1f %% of P_φ). %s'
            % (T1q, T2q, T1m, T2m, (gq + gm) / 2 + F, F, Pphi, tphi, '' if att else ' (a supremum, not attained)', Pst, n,
               best[1], 100 * best[1] / Pphi, verdict))
    return K.result(text, [plot3, plot2])


# ------------------------------------------------------------------ Figure 3: Corollary 8 (prescribed duration)

def _bp_curve(gq, gm, Phi, n, tmax):
    """p_res and B_p on G t = 0..tmax (G = 1), n steps; and the index of the first maximum of e^{mu t} p_res."""
    mu = min(gq, gm)
    dt = tmax / n
    pr = C.p_res_series(1.0, gq, gm, Phi, dt, n)
    w = [math.exp(mu * i * dt) * pr[i] for i in range(n + 1)]
    bp, mx = [], 0.0
    for i in range(n + 1):
        mx = max(mx, w[i])
        bp.append(math.exp(-mu * i * dt) * mx)
    k = 0
    while k < n and w[k + 1] >= w[k]:
        k += 1
    return pr, bp, k


def run_fixed(params):
    p = json.loads(params)
    try:
        Phi = _num(p, 'phi', 0.3, 0.0, 1.5, 'Φ/G')
        gq = _num(p, 'gq', 0.02, 1e-4, 0.5, 'γq/G')
        gm = _num(p, 'gm', 0.002, 1e-5, 0.5, 'γm/G')
    except ValueError as e:
        return K.error(str(e))
    tmax, n = 1.6 * math.pi, 800
    pr, bp, k = _bp_curve(gq, gm, Phi, n, tmax)
    dt = tmax / n
    xs = [i * dt for i in range(n + 1)]
    gain = [b - q for b, q in zip(bp, pr)]
    gmax = max(gain)
    tg = xs[gain.index(gmax)]
    Pphi = C.p_phi(1.0, gq, gm, Phi)[0]
    # 3D data first (the colour scale is shared with the 2D): B_p over (GT, Phi/G); the plain pulse as a lighter sheet
    phis = sorted(set([round(0.05 * i, 6) for i in range(0, 21)] + [round(Phi, 6)]))
    nT = 80
    rows = {}
    for f in phis:
        a, b, kk = _bp_curve(gq, gm, f, nT, tmax)
        rows[f] = (a, b, kk)
    Tg = [i * tmax / nT for i in range(nT + 1)]
    gridB = [[[Tg[i], f, rows[f][1][i]] for f in phis] for i in range(nT + 1)]
    gridP = [[[Tg[i], f, rows[f][0][i]] for f in phis] for i in range(nT + 1)]
    gall = max(1e-9, max(gridB[i][j][2] - gridP[i][j][2] for i in range(nT + 1) for j in range(len(phis))))
    plot2 = K.svg_plot([{'name': 'P_φ (no pulse of any duration is above)', 'x': [0, tmax], 'y': [Pphi, Pphi], 'mode': 'line',
                         'color': '#bbbbbb'},
                        {'name': 'B_p(T): best of any pulse of duration T', 'x': xs, 'y': bp, 'mode': 'line', 'color': PAL[0]},
                        {'name': 'plain resonant pulse of duration T', 'x': xs, 'y': pr, 'mode': 'line', 'color': PAL[1]},
                        {'name': 'dots on B_p coloured by the gain over the plain pulse (same scale as the 3D)',
                         'x': xs[::10], 'y': bp[::10], 'mode': 'points', 'size': 3.5,
                         'colors': [K.scale(g, 0.0, gall, 'sequential') for g in gain[::10]]},
                        {'name': 'first max of e^{μt}p_res (τ_p)', 'x': [xs[k]], 'y': [pr[k]], 'mode': 'points', 'size': 5,
                         'color': PAL[4]}],
                       title='Corollary 8 at Φ = %g G' % Phi, xlabel='duration G·T', ylabel='transferred population',
                       figure='paperfig-3')
    frames, labels = [], []
    for f in phis:
        a, b, kk = rows[f]
        frames.append([K.curve3([[Tg[i], f, b[i]] for i in range(nT + 1)], 'B_p at this Φ', color='#C62828', width=3),
                       K.curve3([[Tg[i], f, a[i]] for i in range(nT + 1)], 'plain pulse at this Φ', color='#111111',
                                width=3, dash=True),
                       K.points3([[Tg[kk], f, a[kk]]], 'τ_p', color='#C62828', size=8, star=True)])
        labels.append('%.2f, gain up to %.3f' % (f, max(x - y for x, y in zip(b, a))))
    surfB = _surf(gridB, 'B_p(T), coloured by the gain over the plain pulse', '#1B6F8C', 0.8)
    surfB['colors'] = [[K.scale(gridB[i][j][2] - gridP[i][j][2], 0.0, gall, 'sequential') for j in range(len(phis))]
                       for i in range(nT + 1)]
    items = [surfB, _surf(gridP, 'plain resonant pulse', '#B5530F', 0.2)]
    plot3 = K.three_d(items, 'B_p over (duration, dephasing): ▶ walks Φ; the colour is the gain over the plain pulse',
                      colorbar=K.colorbar('gain B_p − p_res', 0.0, gall, 'sequential'),
                      axes=('duration G·T', 'Φ/G', 'population'),
                      slider={'label': 'dephasing Φ/G', 'values': labels, 'items': frames, 'start': phis.index(round(Phi, 6))})
    ok_env = all(b >= q - 1e-12 for b, q in zip(bp, pr))
    ok_sup = max(bp) <= Pphi + 1e-9
    text = ('G = 1, γq = %g, γm = %g, Φ = %g. The plain resonant pulse is exactly optimal up to <b>Gτ_p = %.4f</b> (first '
            'maximum of e^{μt}p_res, μ = %g); after it the best protocol is the resonant pulse stopped at its best moment '
            'plus a wait in the less lossy element. Largest gain over the plain pulse: <b>%.4f</b> at GT = %.3f. B_p ≥ '
            'p_res on the whole range: %s; largest B_p = %.5f against P_φ = %.5f (never above it: %s).'
            % (gq, gm, Phi, xs[k], min(gq, gm), gmax, tg, ok_env, max(bp), Pphi, ok_sup))
    return K.result(text, [plot3, plot2])


# ------------------------------------------------------------------ Figure 4: Corollary 10 (p + 2c and the envelopes)

def run_env(params):
    p = json.loads(params)
    try:
        mode = int(_num(p, 'mode', 1, 1, 3, 'the ETH mode'))
        lo = _num(p, 'lo', 1.545, 1.0, 1.58, 'the left end of the window (G t)')
        hi = _num(p, 'hi', 1.580, 1.5, 2.0, 'the right end of the window (G t)')
    except ValueError as e:
        return K.error(str(e))
    if hi < lo + 0.005:
        return K.error('the window must be at least 0.005 wide')
    G = C.G_ETH
    T1q, T2q = C.ETH_Q
    T1m, T2m = C.ETH_MODES[mode]
    E = C.envelopes(G, T1q, T2q, T1m, T2m, max(2.6, hi + 0.05))
    dg = 2e-4
    S = [a + 2 * b for a, b in zip(E['Bp'], E['Bc'])]
    Sr = [a + 2 * b for a, b in zip(E['p'], E['c'])]
    xr, sr = C.peak(Sr, dg)
    xe, se = C.peak(S, dg)
    wc = [math.exp(E['nu'] * t) * c for t, c in zip(E['t'], E['c'])]
    xc = C.peak(wc, dg)[0]
    r_res, r_time = 0.5 - sr / 6, 0.5 - se / 6
    r_sep = C.r_sep(G, T1q, T2q, T1m, T2m)[0]
    i0, i1 = int(lo / dg), int(hi / dg)
    step = max(1, (i1 - i0) // 350)
    ix_all = list(range(i0, i1 + 1, step))
    # the figure of the paper shows only what lies within 60e-6 of the resonant maximum; the rest of the window (the
    # resonant curve falls by hundreds) would flatten the part that matters
    ix = [i for i in ix_all if (Sr[i] - sr) * 1e6 >= -60] or ix_all
    X = [E['gt'][i] for i in ix]
    dS = [(S[i] - sr) * 1e6 for i in ix]
    dR = [(Sr[i] - sr) * 1e6 for i in ix]
    off = 1.5
    dP = [(E['Bp'][i] - E['p'][i]) * 1e6 for i in ix]
    d2C = [2 * (E['Bc'][i] - E['c'][i]) * 1e6 for i in ix]
    # colour = how far the envelopes are above the resonant pulse in p + 2c (light = equal, dark = largest gap): 2D and 3D
    gap = [a + b for a, b in zip(dP, d2C)]
    gtop = max(1e-9, max(gap))
    gcol = [K.scale(g, 0.0, gtop, 'sequential') for g in gap]
    plot2 = K.svg_plot([{'name': 'optimal envelopes B_p + 2B_c', 'x': [(x - off) * 1e3 for x in X], 'y': dS, 'mode': 'line',
                         'color': PAL[1]},
                        {'name': 'dots on the envelopes coloured by the gap over the pulse', 'x': [(x - off) * 1e3 for x in X],
                         'y': dS, 'mode': 'points', 'size': 2.5, 'colors': gcol},
                        {'name': 'resonant pulse p + 2c', 'x': [(x - off) * 1e3 for x in X], 'y': dR, 'mode': 'line',
                         'color': PAL[0]},
                        {'name': 'peak of the resonant pulse', 'x': [(xr - off) * 1e3], 'y': [0.0], 'mode': 'points', 'size': 5,
                         'color': PAL[0]},
                        {'name': 'peak of the envelopes', 'x': [(xe - off) * 1e3], 'y': [(se - sr) * 1e6], 'mode': 'points',
                         'size': 5, 'color': PAL[1]}],
                       title='Corollary 10, ETH mode %d (the part within 6·10⁻⁵ of the maximum)' % mode,
                       xlabel='duration: 1000·(G t − 1.5)', ylabel='p + 2c minus the resonant maximum (×10⁻⁶)',
                       figure='paperfig-4')
    curve =[[(x - off) * 1e3, a, b] for x, a, b in zip(X, dP, d2C)]
    ke = int(round(xe / dg))
    items = [K.curve3(curve, 'both gaps together (Δp, 2Δc)', color='#999999', width=2),
             K.points3(curve, 'coloured by the gap Δp + 2Δc', color='#C62828', size=3.5, colors=gcol, opacity=1.0),
             K.curve3([[(x - off) * 1e3, a, 0.0] for x, a in zip(X, dP)], 'population gap Δp = B_p − p_res (shadow)', color=PAL[0], width=2),
             K.curve3([[(x - off) * 1e3, 0.0, b] for x, b in zip(X, d2C)], 'coherence gap 2Δc = 2(B_c − c_res) (shadow)', color=PAL[2],
                      width=2),
             K.points3([[(xe - off) * 1e3, (E['Bp'][ke] - E['p'][ke]) * 1e6, 2 * (E['Bc'][ke] - E['c'][ke]) * 1e6]],
                       'where p + 2c of the envelopes peaks', color='#111111', size=9, star=True)]
    plot3 = K.three_d(items, 'The two gaps that make the envelopes exceed the pulse, with their shadows',
                      axes=('duration 1000·(G t − 1.5)', 'Δp (×10⁻⁶)', '2Δc (×10⁻⁶)'),
                      colorbar=K.colorbar('gap of p + 2c over the resonant pulse (×10⁻⁶)', 0.0, gtop, 'sequential'))
    equal = xr <= xc
    table = K.table(['quantity', 'value'],
                    [['r_sep (%)', '%.5f' % (100 * r_sep)], ['r_time (%)', '%.5f' % (100 * r_time)],
                     ['r_res (%)', '%.5f' % (100 * r_res)], ['r_res − r_time', '%.2e' % (r_res - r_time)],
                     ['G t_r (resonant maximum)', '%.6f' % xr], ['G t of the envelope maximum', '%.6f' % xe],
                     ['G τ_c (max of e^{νs}c_res)', '%.6f' % xc]])
    text = ('ETH mode %d (transmon T1 = %g, T2 = %g µs; mode T1 = %g, T2 = %g µs; G = 2π·0.296 MHz). The chain of Corollary 10, '
            '<b>r_sep = %.4f %% ≤ r_time = %.5f %% ≤ r_opt ≤ r_res = %.5f %%</b>; the distance r_res − r_time = <b>%.2e</b>. '
            'The envelope peaks %.2e above the resonant peak in p + 2c (×10⁻⁶ in the figure: %.3f). Equality condition '
            '(G t_r &lt; G τ_c): %.5f %s %.5f → %s.'
            % (mode, T1q, T2q, T1m, T2m, 100 * r_sep, 100 * r_time, 100 * r_res, r_res - r_time, se - sr, (se - sr) * 1e6,
               xr, '&lt;' if equal else '&gt;', xc,
               'the resonant pulse is exactly optimal (r_opt = r_res)' if (r_res - r_time) < 1e-9 else
               'a distance remains, so optimality of the resonant pulse is not decided here'))
    return K.result(text, [plot3, plot2], table)


# ------------------------------------------------------------------ Figure 5: Table 3 (Rutgers)

def run_rutgers(params):
    p = json.loads(params)
    try:
        T1q = _num(p, 'T1q', C.RUTGERS_Q[0], 1, 1000, 'the transmon T1(f→e) in µs')
        T2q = _num(p, 'T2q', C.RUTGERS_Q[1], 1, 2000, 'the transmon T2 in µs')
        mode = int(_num(p, 'mode', 1, 1, 10, 'the mode'))
    except ValueError as e:
        return K.error(str(e))
    T2q = min(T2q, 2 * T1q)          # no pure dephasing beyond 2 T1
    modes = list(range(1, 11))
    lim = [C.rutgers_limit(i, T1q, T2q) for i in range(10)]
    sim = [100 * (1 - r[3]) for r in C.RUTGERS]
    rabi = [100 * (1 - r[2]) for r in C.RUTGERS]
    tren = [100 * (1 - r[1]) for r in C.RUTGERS]
    # colour = verdict of the claim "nothing falls below the limit": a value keeps its series colour while it holds and
    # turns red when it falls below the limit of its mode (2D and 3D alike)
    vc = lambda vals, col: [K.verdict(False) if v < l - 1e-12 else col for v, l in zip(vals, lim)]
    plot2 = K.svg_plot([{'x': [0], 'y': [lim[0]], 'mode': 'points', 'size': 0, 'color': '#ffffff'},    # axis from 0: even ticks
                        {'name': 'limit 1 − P_φ', 'x': modes, 'y': lim, 'mode': 'line', 'color': PAL[1]},
                        {'name': 'their simulation (red = below the limit)', 'x': modes, 'y': sim, 'mode': 'points', 'size': 4,
                         'colors': vc(sim, '#777777')},
                        {'name': 'measured, Rabi decay', 'x': modes, 'y': rabi, 'mode': 'points', 'size': 4,
                         'colors': vc(rabi, PAL[0])},
                        {'name': 'measured, pulse train', 'x': modes, 'y': tren, 'mode': 'points', 'size': 4,
                         'colors': vc(tren, PAL[2])},
                        {'name': 'your mode: the limit', 'x': [mode], 'y': [lim[mode - 1]], 'mode': 'points', 'size': 7,
                         'color': PAL[4]}],
                       title='Table 3 as a picture', xlabel='cavity mode', ylabel='error per exchange (%)',
                       figure='paperfig-5')
    below = []
    for name, ser in (('simulation', sim), ('Rabi decay', rabi), ('pulse train', tren)):
        below += [(name, i + 1) for i in range(10) if ser[i] < lim[i] - 1e-12]
    ks = _geom(0.25, 4.0, 9)
    grid = [[[m, math.log10(k), C.rutgers_limit(m - 1, T1q * k, min(T2q * k, 2 * T1q * k), refine=False)] for k in ks]
            for m in modes]
    zhi = max(z for row in grid for _, _, z in row)
    zlo = min(z for row in grid for _, _, z in row)
    items = [_surf(grid, 'the limit 1 − P_φ (colour = its value)', '#B5530F', 0.6,
                   lambda x, y, z: K.scale(z, zlo, zhi, 'sequential')),
             K.points3([[m, 0.0, v] for m, v in zip(modes, sim)], 'their simulation', color='#777777', size=6,
                       colors=vc(sim, '#777777')),
             K.points3([[m, 0.0, v] for m, v in zip(modes, rabi)], 'measured, Rabi decay', color='#1B6F8C', size=6,
                       colors=vc(rabi, '#1B6F8C')),
             K.points3([[m, 0.0, v] for m, v in zip(modes, tren)], 'measured, pulse train', color='#2E7D32', size=6,
                       colors=vc(tren, '#2E7D32')),
             K.points3([[mode, 0.0, lim[mode - 1]]], 'your mode, the limit', color='#C62828', size=9, star=True)]
    plot3 = K.three_d(items, 'The limit as the transmon times are multiplied (y = log10 factor; the data sit at factor 1)',
                      axes=('cavity mode', 'log10 of transmon-time factor', 'error (%)'),
                      colorbar=K.colorbar('limit 1 − P_φ (%); data points turn RED when below it', zlo, zhi, 'sequential'))
    rows = [[m, '%.1f' % C.RUTGERS[m - 1][0], '%.3f' % lim[m - 1], '%.3f' % sim[m - 1], '%.3f' % rabi[m - 1],
             '%.3f' % tren[m - 1], '%.1f' % (rabi[m - 1] / lim[m - 1])] for m in modes]
    table = K.table(['mode', 'τπ (ns)', 'limit %', 'simulation %', 'Rabi %', 'train %', 'Rabi / limit'], rows)
    text = ('Transmon T1(f→e) = %g µs, T2 = %g µs; G = π/(2τπ) per mode, cavity times from the paper. Of the 30 values '
            '(simulation, Rabi decay, pulse train) <b>%d fall below the limit</b>%s. Mode %d: limit %.3f %%, Rabi decay '
            '%.3f %% (×%.2f), pulse train %.3f %%, simulation %.3f %%. With the paper’s transmon times (28.85 and 36.58) '
            'none is below; the claim depends on the transmon times, and G taken from τπ includes ramps (the limit is that '
            'of a rectangular pulse of the same duration).'
            % (T1q, T2q, len(below), '' if not below else ' (%s)' % ', '.join('%s of mode %d' % b for b in below[:6]),
               mode, lim[mode - 1], rabi[mode - 1], rabi[mode - 1] / lim[mode - 1], tren[mode - 1], sim[mode - 1]))
    return K.result(text, [plot3, plot2], table)


# ------------------------------------------------------------------ Figure 6: r_res over coupling and transmon times

_LEVELS = [0.02, 0.05, 0.1, 0.2, 0.3, 0.5, 0.7, 1.01]
_COLS = ['#fde725', '#a0da39', '#4ac16d', '#1fa187', '#277f8e', '#365c8d', '#46327e']


def _bin(v):
    for i in range(len(_LEVELS) - 1):
        if v < _LEVELS[i + 1]:
            return i
    return len(_COLS) - 1


def _heatmap(ka, kb, Z, a0, b0, text):
    W, H, L, R, T, B = 560, 400, 60, 16, 24, 90
    la, lb = math.log(ka[0]), math.log(kb[0])
    sa, sb = math.log(ka[-1]) - la, math.log(kb[-1]) - lb
    la, lb, sa, sb = la - 0.07 * sa, lb - 0.07 * sb, 1.14 * sa, 1.14 * sb      # a margin: the dot never touches the frame
    X = lambda a: L + (math.log(a) - la) / sa * (W - L - R)
    Y = lambda b: H - B - (math.log(b) - lb) / sb * (H - T - B)
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (W, H + 30)]
    na, nb = len(ka), len(kb)
    for j in range(nb):
        yl = Y(math.sqrt(kb[j] * kb[j - 1])) if j > 0 else Y(kb[0])
        yh = Y(math.sqrt(kb[j] * kb[j + 1])) if j < nb - 1 else Y(kb[-1])
        for i in range(na):
            xl = X(math.sqrt(ka[i] * ka[i - 1])) if i > 0 else X(ka[0])
            xh = X(math.sqrt(ka[i] * ka[i + 1])) if i < na - 1 else X(ka[-1])
            o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" stroke="%s" stroke-width="0.4"/>'
                     % (xl, yh, xh - xl + 0.6, yl - yh + 0.6, _COLS[_bin(Z[j][i])], _COLS[_bin(Z[j][i])]))
    for v in (1, 2, 4, 8):
        if ka[0] <= v <= ka[-1]:
            o.append('<text x="%.1f" y="%d" font-size="10" text-anchor="middle">%g</text>' % (X(v), H - B + 14, v))
    for v in (0.5, 1, 3, 10, 30):
        if kb[0] <= v <= kb[-1]:
            o.append('<text x="%d" y="%.1f" font-size="10" text-anchor="end">%g</text>' % (L - 4, Y(v) + 3, v))
    o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="none" stroke="#888"/>' % (L, T, W - L - R, H - T - B))
    o.append('<text x="%d" y="%d" text-anchor="middle" font-size="12">coupling factor</text>' % ((W + L - R) / 2, H - B + 30))
    o.append('<text x="14" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 14 %d)">transmon-times factor</text>'
             % ((H - B + T) / 2, (H - B + T) / 2))
    o.append('<circle cx="%.1f" cy="%.1f" r="7" fill="#D55E00" stroke="#fff" stroke-width="1.5"/>' % (X(a0), Y(b0)))
    labs = ['%g–%g' % (_LEVELS[i], _LEVELS[i + 1]) if i < len(_COLS) - 1 else '%g–%g' % (_LEVELS[i], _LEVELS[i + 1])
            for i in range(len(_COLS))]
    labs[0] = '&lt; %g' % _LEVELS[1]
    labs[-1] = '≥ %g' % _LEVELS[-2]
    for i, c in enumerate(_COLS):
        x = L + i * 70
        o.append('<rect x="%d" y="%d" width="14" height="10" fill="%s"/><text x="%d" y="%d" font-size="10">%s</text>'
                 % (x, H - 38, c, x + 17, H - 29, labs[i]))
    o.append('<text x="%d" y="%d" font-size="10">limit r_res (%%); orange dot: your device. %s</text>' % (L, H - 12, text))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': 'Level map of r_res (%)', 'figure': 'paperfig-6'}


def run_surface(params):
    p = json.loads(params)
    try:
        a0 = _num(p, 'a', 1.0, 0.5, 8, 'the coupling factor')
        b0 = _num(p, 'b', 1.0, 0.5, 30, 'the transmon-times factor')
        c0 = _num(p, 'c', 1.0, 0.5, 100, 'the phonon-times factor')
    except ValueError as e:
        return K.error(str(e))
    G0 = C.G_ETH
    T1q, T2q = C.ETH_Q
    T1m, T2m = C.ETH_MODES[1]

    def rr(a, b, refine=False):
        return 100 * C.r_res(G0 * a, T1q * b, T2q * b, T1m * c0, T2m * c0, refine)[0]
    mine = rr(a0, b0, True)
    base = 100 * C.r_res(G0, T1q, T2q, T1m, T2m)[0]
    N = 18
    ka = _geom(min(1.0, a0), max(4.0, a0), N)
    kb = _geom(min(1.0, b0), max(10.0, b0), N)
    Z = [[rr(a, b) for a in ka] for b in kb]
    plot2 = _heatmap(ka, kb, Z, a0, b0, 'Yours: %.4f %%.' % mine)
    grid = [[[math.log10(ka[i]), math.log10(kb[j]), Z[j][i]] for j in range(N)] for i in range(N)]
    frames, labels = [], []
    for j in range(N):
        frames.append([K.curve3([[math.log10(ka[i]), math.log10(kb[j]), Z[j][i]] for i in range(N)],
                                'coupling sweep at this transmon factor', color='#C62828', width=3)])
        labels.append('%.2f' % kb[j])
    j0 = min(range(N), key=lambda j: abs(math.log(kb[j]) - math.log(b0)))
    items = [_surf(grid, 'r_res (%), coloured by the same bands as the level map', '#1B6F8C', 0.85,
                   lambda x, y, z: _COLS[_bin(z)]),
             K.points3([[math.log10(a0), math.log10(b0), mine]], 'your device', color='#D55E00', size=9, star=True)]
    plot3 = K.three_d(items, 'The limit over (coupling, transmon times); ▶ sweeps the transmon factor',
                      axes=('log10 coupling ×', 'log10 transmon times ×', 'r_res (%)'),
                      colorbar=K.colorbar('r_res (%), bands of the level map',
                                          stops=[[('< 0.05' if i == 0 else ('≥ 0.5' if False else '%g–%g' % (_LEVELS[i], _LEVELS[i + 1]))),
                                                  c] for i, c in enumerate(_COLS)]),
                      slider={'label': 'transmon times', 'values': labels, 'items': frames, 'start': j0})
    text = ('ETH mode 1 (phonon T1 = %g, T2 = %g µs, times ×%g; transmon T1 = %g, T2 = %g µs ×%g; coupling G = 2π·0.296 MHz ×%g). '
            '<b>r_res = %.4f %%</b>%s. The present device (all factors 1, phonon kept as it is) gives %.4f %%; your device is '
            '<b>×%.2f</b> of it.'
            % (T1m * c0, T2m * c0, c0, T1q * b0, T2q * b0, b0, a0, mine, '' if c0 == 1 else ' (phonon ×%g)' % c0, base,
               mine / base))
    return K.result(text, [plot3, plot2])


# ------------------------------------------------------------------ the memory cycle without reset

_CYCLE_DEV = {1: ('ETH mode 1', C.G_ETH, (30.0, 23.0, 196.0, 368.0)), 2: ('ETH mode 2', C.G_ETH, (30.0, 23.0, 137.0, 250.0)),
              3: ('ETH mode 3', C.G_ETH, (30.0, 23.0, 64.0, 127.0)),
              4: ('Caltech oscillator A', C.G_CALTECH_A, C.CALTECH_A)}


def _best_exact(G, T, t):
    """Exact cost of the best pair of equal resonant pulses (read phase π) over the parking angle: (r, delta)."""
    d = [0.5 * i / 12 for i in range(13)]
    vals = [C.cycle_exact(G, *T, t, math.pi / 2 - x) for x in d]
    k = min(range(13), key=lambda i: vals[i])
    a, b = math.pi / 2 - d[min(k + 1, 12)], math.pi / 2 - d[max(k - 1, 0)]
    th, v = C._golden_max(lambda th: -C.cycle_exact(G, *T, t, th), a, b, it=20)
    return -v, math.pi / 2 - th


def run_cycle(params):
    p = json.loads(params)
    try:
        mode = int(_num(p, 'mode', 1, 1, 4, 'the device'))
        s = _num(p, 'scale', 1.0, 0.01, 3.0, 'the rate factor')
        t = _num(p, 't', 10.0, 0.2, 200.0, 'the wait t (µs)')
        raw = str(p.get('delta', 'auto')).strip().lower()
        d_in = None if raw in ('', 'auto') else float(raw.replace(',', '.')) / 1000.0
        if d_in is not None and not (0 <= d_in <= 0.3):
            raise ValueError('the parking offset must be between 0 and 300 mrad (or "auto")')
    except ValueError as e:
        return K.error(str(e) if 'must' in str(e) else 'the parking offset is a number in mrad, or "auto"')
    name, G, T0 = _CYCLE_DEV[mode]
    T = tuple(x / s for x in T0)                       # rates × s  <=>  times / s
    gq, gm, eq, em, fq, fm = C.rates(*T)
    par = (gq, gm, fq, fm)
    gain_c, dstar_c = C.gain_closed(G, par, t)
    r1star, thstar = C.r1_min(G, par, t)
    r1reset = C.r1_cycle(G, par, t, math.pi / 2)
    dstar_num = math.pi / 2 - thstar
    d_use = d_in if d_in is not None else (dstar_c if dstar_c is not None else 0.0)
    r1_me = C.r1_cycle(G, par, t, math.pi / 2 - d_use)
    floor = C.floor_with_reset(G, *T, t)
    ex_full = C.cycle_exact(G, *T, t, math.pi / 2)
    ex_me = C.cycle_exact(G, *T, t, math.pi / 2 - d_use)
    ex_best, d_ex = _best_exact(G, T, t)
    idle = C.idle_cost(T[0], T[1], t)
    # the curves against the parking offset: wide enough to show both optima, cut where the gain falls far below the
    # peak (a quadratic keeps falling and would flatten what matters)
    dmax = min(0.3, max(0.004, 6 * max(dstar_c or 0.0, d_ex, d_use)))
    ds = _lin(0.0, dmax, 121)
    g1 = [(r1reset - C.r1_cycle(G, par, t, math.pi / 2 - x)) * 1e6 for x in ds]
    exs = [C.cycle_exact(G, *T, t, math.pi / 2 - x) for x in ds]
    gx = [(ex_full - v) * 1e6 for v in exs]
    peak_g = max(max(g1), max(gx), 1e-6)
    keep = [i for i in range(len(ds)) if min(g1[i], gx[i]) >= -2.5 * peak_g] or list(range(len(ds)))
    kd = [ds[i] for i in keep]
    plotA = K.svg_plot([{'name': 'first-order gain r₁(0) − r₁(δ)', 'x': kd, 'y': [g1[i] for i in keep], 'mode': 'line',
                         'color': PAL[1]},
                        {'name': 'exact two-pulse gain r(0) − r(δ)', 'x': kd, 'y': [gx[i] for i in keep], 'mode': 'line',
                         'color': PAL[0]},
                        {'name': 'your δ (first order, exact)', 'x': [d_use, d_use],
                         'y': [(r1reset - r1_me) * 1e6, (ex_full - ex_me) * 1e6], 'mode': 'points', 'size': 5,
                         'color': PAL[4]}] +
                       ([{'name': 'δ* (closed form)', 'x': [dstar_c, dstar_c], 'y': [0, peak_g], 'mode': 'line',
                          'color': '#999999'}] if dstar_c and dstar_c <= kd[-1] else []),
                       title='Leaving the swap unfinished by δ: gain over the full swap (×10⁻⁶)',
                       xlabel='parking offset δ = π/2 − Gt_w (rad)', ylabel='gain in r (×10⁻⁶)')
    # 3D: the first-order gain over (log10 t, delta); the grid follows the valley (delta = u delta*(t)), so the ridge
    # of height gain(t) and its decay with t are drawn at their true place
    c_d = (dstar_c * t) if dstar_c else None                      # delta*(t) = c_d / t  (closed form)
    t_lo = max(0.5, (c_d / 0.12) if c_d else 0.5)
    ts = _geom(t_lo, 100.0, 16)
    us = _lin(0.0, 2.5, 15)
    gridR, valley, dfl = [], [], []          # dfl: exact cost minus the floor with reset at each vertex (colour)
    for tt in ts:
        dstar_t = (c_d / tt) if c_d else 0.02
        row, frow = [], []
        r0 = C.r1_cycle(G, par, tt, math.pi / 2, 160)
        fl = C.floor_with_reset(G, *T, tt)
        for u in us:
            dd = u * dstar_t
            row.append([30 * math.log10(tt), dd * 1e3, (r0 - C.r1_cycle(G, par, tt, math.pi / 2 - dd, 160)) * 1e6])
            frow.append((C.cycle_exact(G, *T, tt, math.pi / 2 - dd) - fl) * 1e6)
        gridR.append(row)
        dfl.append(frow)
        if c_d:
            valley.append([30 * math.log10(tt), dstar_t * 1e3, (r0 - C.r1_cycle(G, par, tt, math.pi / 2 - dstar_t, 160)) * 1e6])
    # colour = exact two-pulse cost minus the floor of the cycle WITH a reset (centre 0): blue below the floor (the floor
    # is not a bound there), red above it; the same code in plotB. Height = first-order gain.
    dlo = min(-1e-9, min(min(r) for r in dfl))
    dhi = max(1e-9, max(max(r) for r in dfl))
    surfR = _surf(gridR, 'first-order gain, coloured by exact cost − floor with reset', '#1B6F8C', 0.85)
    surfR['colors'] = [[K.scale(v, dlo, dhi, 'diverging', 0.0) for v in r] for r in dfl]
    items = [surfR]
    if len(valley) > 1:
        items.append(K.curve3(valley, 'top of the ridge δ*(t) (closed form)', color='#C62828', width=3))
    if t >= t_lo and d_use <= 2.5 * ((c_d / t) if c_d else 0.02):
        items.append(K.points3([[30 * math.log10(t), d_use * 1e3, (r1reset - r1_me) * 1e6]], 'your t and δ', color='#111111', size=9,
                               star=True))
    plot3 = K.three_d(items, 'First-order gain over (wait, offset): a ridge that falls as 1/t',
                      axes=('30·log10 t (t in µs)', 'offset δ (mrad)', 'gain (×10⁻⁶)'),
                      colorbar=K.colorbar('exact cost − floor with reset (×10⁻⁶): blue = below the floor, red = above',
                                          dlo, dhi, 'diverging', 0.0))

    plotB = K.svg_plot([{'name': 'exact two resonant pulses minus the floor WITH reset', 'x': kd,
                         'y': [(exs[i] - floor) * 1e6 for i in keep], 'mode': 'line', 'color': PAL[0]},
                        {'name': 'zero: the floor of the cycle with a reset', 'x': [kd[0], kd[-1]], 'y': [0, 0], 'mode': 'line',
                         'color': PAL[2]},
                        {'name': 'dots coloured as the 3D (blue below the floor, red above)', 'x': kd,
                         'y': [(exs[i] - floor) * 1e6 for i in keep], 'mode': 'points', 'size': 3,
                         'colors': [K.scale((exs[i] - floor) * 1e6, dlo, dhi, 'diverging', 0.0) for i in keep]}],
                       title='Below zero the floor with a reset is not a bound (×10⁻⁶)', xlabel='parking offset δ (rad)',
                       ylabel='exact r minus the floor (×10⁻⁶)')
    cross = None
    f = lambda tt: _best_exact(G, T, tt)[0] - C.idle_cost(T[0], T[1], tt)
    if f(0.05) > 0 > f(300.0):
        lo_, hi_ = 0.05, 300.0
        for _ in range(12):
            mid = math.sqrt(lo_ * hi_)
            if f(mid) > 0:
                lo_ = mid
            else:
                hi_ = mid
        cross = math.sqrt(lo_ * hi_)
    eps = max(gq, gm, fq, fm) * math.pi / (2 * G)
    tc, thc = C.t_c_first_order(G, par)
    if tc is None:
        tc_txt = ('γm+φm ≥ γq+φq: by the proposition, not accessing the memory is optimal at first order for every '
                  'wait')
    else:
        tc_txt = ('the first-order memory-utility threshold is <b>t_c = %.4f µs</b> (angle %.4f rad): for t &lt; t_c not '
                  'accessing is optimal, above it a write to a finite angle pays; your t = %g µs is %s t_c'
                  % (tc, thc, t, 'below' if t < tc else 'above'))
    table = K.table(['quantity', 'value'],
                    [['first-order memory-utility threshold t_c (µs)', '%.5f' % tc if tc else 'none (γm+φm ≥ γq+φq)'],
                     ['first-order cost with parking in the memory, r₁(π/2) (%)', '%.5f' % (100 * r1reset)],
                     ['first-order minimum r₁* (%)', '%.5f' % (100 * r1star)],
                     ['first-order gain r₁(π/2) − r₁*', '%.3e' % (r1reset - r1star)],
                     ['large-t gain (γm+φm)²/(3G²(γq+2φq−γm)t), valid when γm+φm < γq+φq',
                      '%s' % ('%.3e' % gain_c if gain_c and tc else 'not applicable (γm+φm ≥ γq+φq)')],
                     ['δ* closed form / numerical (rad)', '%s / %.5f' % ('%.5f' % dstar_c if dstar_c else '—', dstar_num)],
                     ['exact cost, two full swaps (%)', '%.6f' % (100 * ex_full)],
                     ['exact cost, two pulses at your δ (%)', '%.6f' % (100 * ex_me)],
                     ['exact cost, best δ = %.5f rad (%%)' % d_ex, '%.6f' % (100 * ex_best)],
                     ['floor WITH reset (Prop.) (%)', '%.6f' % (100 * floor)],
                     ['waiting in the qubit, exact (%)', '%.6f' % (100 * idle)]])
    text = ('%s, rates × %g, wait t = %g µs. To first order in the rates, for cycles that close without noise '
            '(Proposition: written proof; the numbers here are computed in floating point), the cycle without reset '
            'costs at least r₁(θ) = (2/G)∫₀^θ ρ(cos²u)du + t·ρ(cos²θ) (θ = Gt_w the angle at which it parks); %s. '
            'The minimum is at δ* = π/2 − θ* = <b>%s rad</b> (large-t closed form %s) and gains <b>%s</b> over parking in the memory '
            '(closed form %s). The exact dynamics of two resonant pulses with read phase π (4-variable Lindblad block, this '
            'is exact for that protocol, not a global optimum) gives %.6f %% at the best δ = %.4f rad against the floor %.6f %% '
            'of the cycle WITH a reset: the floor %s a bound without reset for this wait. ρ is first order only (here '
            'ε ≈ %.3f%s; the residual O(ε²) is not bounded uniformly). Idle in the qubit costs %.6f %%%s.'
            % (name, s, t, tc_txt, '%.5f' % dstar_num, '%.5f' % dstar_c if dstar_c else 'none', '%.3e' % (r1reset - r1star),
               '%.3e' % gain_c if gain_c else 'none', 100 * ex_best, d_ex, 100 * floor,
               'is NOT' if ex_best < floor - 1e-9 else 'remains', eps,
               ' — not small: do not trust the first-order numbers' if eps > 0.1 else '', 100 * idle,
               ('; waiting in the qubit beats the memory cycle for t below about %.2f µs' % cross) if cross else ''))
    return K.result(text, [plot3, plotA, plotB], table)


# ------------------------------------------------------------------ Proposition prop:strong (strong dephasing, no relaxation)

SQ5 = math.sqrt(5.0)


def _f_min_equal(phi):
    """min over 0 < T <= pi/2 of f_phi(T) = W_phi(T) - 4 sin T, W = e^{phi T} z(T) (G = 1, phi >= 2; convex there): float."""
    def f(T):
        z, _ = C.res_zc(phi, 0.0, T)
        return math.exp(phi * T) * z - 4 * math.sin(T)
    lo, hi = 1e-9, math.pi / 2
    for _ in range(120):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(m1) < f(m2):
            hi = m2
        else:
            lo = m1
    T = (lo + hi) / 2
    return f(T), T


def run_strong(params):
    p = json.loads(params)
    try:
        pq = _num(p, 'phiq', 3.0, 0.0, 60.0, 'φq/G')
        pm = _num(p, 'phim', 3.0, 0.0, 60.0, 'φm/G')
        raw = str(p.get('T', 'auto')).strip().lower()
        if raw in ('', 'auto'):
            Tin = None
        else:
            Tin = float(raw.replace(',', '.'))
            if not (0.5 <= Tin <= 300):
                raise ValueError('the longest duration G·T must be between 0.5 and 300 (or "auto")')
    except ValueError as e:
        return K.error(str(e) if 'must' in str(e) else 'the longest duration G·T is a number, or "auto"')
    a, d = (pq + pm) / 2, abs(pq - pm) / 2
    prod, D = pq * pm, abs(pq - pm)
    kap = math.sqrt(a * a - 4) if a > 2 else 0.0
    rate = (a - kap) if a > 2 else max(a, 1e-3)
    tmax = Tin if Tin else min(200.0, max(5.0, 8.0 / rate))
    n = 400
    ts = [tmax * i / n for i in range(1, n + 1)]
    ex = [C.res_pc(pq, pm, t)[2] + 0.5 for t in ts]                 # p + 2c
    iM = max(range(n), key=lambda i: ex[i])
    Rs = []
    for t in ts:
        z, c = C.res_zc(a, d, t)
        Rs.append(4 * c / z if z > 1e-300 and c > 0 else None)
    xr = [t for t, r in zip(ts, Rs) if r is not None]
    yr = [r for r in Rs if r is not None]
    plotA = K.svg_plot([{'name': 'p + 2c of the resonant pulse', 'x': ts, 'y': ex, 'mode': 'line', 'color': PAL[0]},
                        {'name': '1/2 (above it the pulse beats 5/12)', 'x': [0, tmax], 'y': [0.5, 0.5], 'mode': 'line',
                         'color': PAL[1]},
                        {'name': 'largest value in the window', 'x': [ts[iM]], 'y': [ex[iM]], 'mode': 'points', 'size': 5,
                         'color': PAL[4]}],
                       title='The resonant pulse: p + 2c against 1/2', xlabel='duration G·T', ylabel='p + 2c')
    series = [{'name': '4c/(1 − 2p) of the resonant pulse (p + 2c > 1/2 exactly when it exceeds 1)', 'x': xr, 'y': yr,
               'mode': 'line', 'color': PAL[0]},
              {'name': 'the value 1', 'x': [0, tmax], 'y': [1, 1], 'mode': 'line', 'color': PAL[1]}]
    plotB = K.svg_plot(series, title='The same sign, magnified: 4c/(1 − 2p) (log scale)', xlabel='duration G·T',
                       ylabel='4c/(1 − 2p)', logy=True) if len(xr) > 1 else None
    # 3D: the sign of the resonant pulse over (phi_q, phi_m): z = log10 of the largest 4c/(1-2p) for 0 < GT <= 100
    # (float, clipped to +-1.5; +inf where p alone passes 1/2); red = the resonant pulse beats 5/12 somewhere in the window
    hi = max(8.0, 1.15 * max(pq, pm))
    lo = 0.3
    ax = _lin(lo, hi, 17)
    clip = lambda v: max(-1.5, min(1.5, v))
    gridZ = [[[x, y, clip(C.strong_logR_max(x, y))] for y in ax] for x in ax]
    zpt = clip(C.strong_logR_max(pq, pm))
    items = [_surf(gridZ, 'log10 of the largest 4c/(1−2p), G·T ≤ 100 (red: the resonant pulse beats 5/12)', '#1B6F8C', 0.8,
                   lambda x, y, z: K.scale(z, -1.5, 1.5, 'diverging', 0.0))]
    hyp = lambda P: [[x, P / x, 0.0] for x in _geom(max(lo, P / hi), hi, 40) if lo <= P / x <= hi]
    items.append(K.curve3(hyp(3.0), 'φqφm = 3G² (the exact threshold for |φq−φm| ≥ 2√5 G)', color='#111111', width=3))
    items.append(K.curve3(hyp(4.0), 'φqφm = 4G² (where the envelope bound certifies)', color='#7B1FA2', width=3, dash=True))
    for Dl, nm, col in ((2.0, '|φq−φm| = 2G (δ = G)', '#E69F00'), (2 * SQ5, '|φq−φm| = 2√5 G', '#C62828')):
        for sg in (1, -1):
            seg = [[x, x - sg * Dl, 0.0] for x in _lin(lo, hi, 30) if lo <= x - sg * Dl <= hi]
            if len(seg) > 1:
                items.append(K.curve3(seg, nm if sg == 1 else None, color=col, width=2, dash=True))
    items.append(K.points3([[pq, pm, zpt]], 'your point', color='#111111', size=9, star=True))
    plot3 = K.three_d(items, 'Where the resonant pulse beats 5/12: the two hyperbolas and the two asymmetry lines',
                      axes=('φq / G', 'φm / G', 'log10 max 4c/(1−2p)'),
                      colorbar=K.colorbar('log10 of the largest 4c/(1−2p) (blue: the resonant pulse stays below 5/12 in the '
                                          'window; red: above)', -1.5, 1.5, 'diverging', 0.0))
    # --- the three statements of the proposition
    lines = []
    lines.append('φq = %g G, φm = %g G (no relaxation), so φq+φm = %.5f G, φqφm = %.5f G², |φq−φm| = %.5f G (2√5 G = %.5f G).'
                 % (pq, pm, pq + pm, prod, D, 2 * SQ5))
    equal = D <= 1e-9 * max(1.0, pq, pm)
    lo_s, hi_s = float(C.PHI_STAR_LO), float(C.PHI_STAR_HI)
    if equal:
        phi = pq
        if phi < lo_s:
            vd = ('<b>below φ*</b>: by the proposition the resonant pulse itself reaches r &lt; 5/12 at a finite duration, so '
                  'r_opt &lt; 5/12')
        elif phi > hi_s:
            vd = ('<b>above φ*</b>: by the proposition r_opt = r_res = 5/12 and no pulse of finite duration attains it')
        else:
            vd = ('<b>inside the certified enclosure</b> of φ*: the printed digits cannot say on which side you are '
                  '(at φ* itself r_opt = 5/12 and the resonant pulse attains it at one finite duration)')
        s_a = ('(a) Equal rates, φ = %g G. The paper certifies, by interval arithmetic, %s &lt; φ*/G &lt; %s (digits copied '
               'from the paper, not recomputed here): you are %s.' % (phi, C.PHI_STAR_LO, C.PHI_STAR_HI, vd))
        if phi >= 2:
            fm, Tm = _f_min_equal(phi)
            s_a += (' Floating-point look at the criterion: min over 0 &lt; GT ≤ π/2 of f(T) = W(T) − 4 sin T is %.3e at '
                    'GT = %.4f (negative: the resonant pulse beats 5/12 there; positive: it does not; too close to zero '
                    'for floating point to decide, the certified enclosure above does).' % (fm, Tm))
        else:
            s_a += (' For φ &lt; 2G the population of the resonant pulse alone rises above 1/2 at suitable times '
                    '(largest p in the window here: %.4f).' % max(C.res_pc(pq, pm, t)[0] for t in ts))
        lines.append(s_a)
    else:
        lines.append('(a) Not applicable: the rates are different (the equal-rate threshold φ* is for φq = φm).')
    if D >= 2 * SQ5 - 1e-12:
        if prod >= 3:
            vb = ('φqφm = %.5f G² ≥ 3G²: for fixed-phase controls at zero detuning with 0 ≤ g ≤ G, r_opt = 5/12 exactly '
                  'and it is not attained (the proposition for very unequal rates; every such pulse has p + 2c &lt; 1/2)' % prod)
        else:
            vb = ('φqφm = %.5f G² &lt; 3G²: the resonant pulse has p + 2c &gt; 1/2 at all long enough durations, so '
                  'r_opt &lt; 5/12 (the proposition for very unequal rates, part (b))' % prod)
        lines.append('(b) Unequal rates with |φq−φm| ≥ 2√5 G: ' + vb + '.')
    elif equal:
        lines.append('(b) Not applicable: |φq−φm| = 0 &lt; 2√5 G.')
    else:
        extra = ''
        if 1 < d < SQ5:
            extra = (' For 2G &lt; |φq−φm| &lt; 2√5 G the lab of the corollary below 2√5 G gives P_suf(δ) = %.5f G² here '
                     '(δ = %.4f G).' % (C.psuf(d), d))
        lines.append('(b) Not applicable: |φq−φm| = %.5f G is below 2√5 G = %.5f G, where the threshold 3G² is proved. '
                     'Known there: the envelope bound certifies 5/12 from 4G² (φqφm = %.5f G²: %s).%s'
                     % (D, 2 * SQ5, prod, 'reached' if prod >= 4 else 'not reached', extra))
    mx = ex[iM]
    if any(r is None for r in Rs) and any(C.res_zc(a, d, t)[0] <= 0 for t in ts):
        sgn = ('already the population p of the resonant pulse exceeds 1/2 (1 − 2p ≤ 0) in this window, so p + 2c &gt; 1/2 '
               'from then on')
    elif mx > 0.5:
        sgn = 'p + 2c rises above 1/2: largest %.6f at GT = %.3f, i.e. %+.3e over 1/2' % (mx, ts[iM], mx - 0.5)
    else:
        sgn = ('p + 2c stays below 1/2 in the window: largest %.9f at GT = %.3f; its distance %.3e to 1/2 shrinks with the '
               'slowest decay rate' % (mx, ts[iM], 0.5 - mx))
        if D >= 2 * SQ5 - 1e-12 and prod < 3:
            sgn += ('; the proposition says it crosses 1/2 at longer durations than this window: raise the longest GT, or '
                    'read the right-hand plot, where 4c/(1−2p) rises towards 1 and beyond')
    lines.append('(c) The resonant pulse, GT up to %g (closed forms of the paper, floating point, not certified): %s.' % (tmax, sgn))
    lines.append('Strong dephasing in the strict sense: min(φq, φm) %s 4G, %s.' % (
        '≥' if min(pq, pm) >= 4 else '&lt;',
        'so r_opt = r_res = 5/12 for every pulse of finite duration, not attained (proposition, written proof)'
        if min(pq, pm) >= 4 else 'so the first claim of the proposition (all controls) is not the one that applies'))
    plots = [plot3, plotA] + ([plotB] if plotB else [])
    return K.result('<br>'.join(lines), plots)


# ------------------------------------------------------------------ Corollary cor:unequal (sufficient region below 2 sqrt 5 G)

def _psuf_margins(delta, prod):
    """The three scalar margins of the proof at the product prod (G = 1): a+delta-4, (k-Om)s-log(2/Om), (a-delta^2/Om)s-log(2/Om)."""
    om = math.sqrt(delta * delta - 1.0)
    s = math.atanh(om / delta) / om
    a = math.sqrt(delta * delta + prod)
    kk = math.sqrt(a * a - 4.0) if a * a >= 4 else float('nan')
    lg = math.log(2.0 / om)
    return a + delta - 4, (kk - om) * s - lg, (a - delta * delta / om) * s - lg


def run_unequal(params):
    p = json.loads(params)
    try:
        pq = _num(p, 'phiq', 4.77, 0.0, 60.0, 'φq/G')
        pm = _num(p, 'phim', 0.775, 0.0, 60.0, 'φm/G')
    except ValueError as e:
        return K.error(str(e))
    d = abs(pq - pm) / 2
    D, prod = 2 * d, pq * pm
    if d <= 1.0:
        return K.error('δ = |φq−φm|/2 = %.4f G is not above G: the corollary does not apply (Ω = √(δ²−G²) is not '
                       'real). Between 1.72 G and 2 G in |φq−φm| the paper has only the envelope bound, which certifies '
                       '5/12 from φqφm = 4G² (the exact threshold, between 3G² and 4G², is open); below about 1.72 G the '
                       'region is bounded by the tangency of f, numerically. Choose |φq−φm| above 2G.' % d)
    if d >= SQ5:
        return K.error('δ = %.4f G is not below √5 G: the corollary is for 1 < δ < √5 G. For |φq−φm| ≥ 2√5 G '
                       '(= %.4f G) the proposition for very unequal rates applies and the threshold is exactly φqφm = 3G²: your product '
                       '%.5f G² is %s 3G², so %s.'
                       % (d, 2 * SQ5, prod, 'at or above' if prod >= 3 else 'below',
                          'r_opt = 5/12, not attained, for fixed-phase zero-detuning pulses with 0 ≤ g ≤ G' if prod >= 3
                          else 'r_opt is below 5/12'))
    terms, om, s, L = C.psuf_terms(d)
    Ps = max(terms)
    act = ['16 − 8δ', '3 + 2ΩL + L²', '(δ²/Ω + L)² − δ²'][terms.index(Ps)]
    mg = _psuf_margins(d, prod)
    inside = prod >= Ps
    # 2D: P_suf against |phi_q - phi_m| with its three terms, 3G^2 and 4G^2, and the reader's point
    ymax = 12.0
    dg = [x for x in _lin(1.06, SQ5 - 1e-3, 120)]
    cur = [(2 * x, C.psuf_terms(x)[0]) for x in dg]
    cut = lambda col: [(x, v) for x, v in col if v <= ymax]
    ps_c = [(2 * x, max(t)) for x, t in zip(dg, [c[1] for c in cur])]
    ps_c = cut(ps_c)
    ser = [{'name': 'P_suf(δ): you are above it when the point is over this curve', 'x': [a for a, _ in ps_c],
            'y': [b for _, b in ps_c], 'mode': 'line', 'color': PAL[0]}]
    for k, nm in enumerate(('16 − 8δ', '3 + 2ΩL + L²', '(δ²/Ω + L)² − δ²')):
        cc = cut([(2 * x, t[k]) for x, t in zip(dg, [c[1] for c in cur])])
        if len(cc) > 1:
            ser.append({'name': 'term: ' + nm, 'x': [a for a, _ in cc], 'y': [b for _, b in cc], 'mode': 'line',
                        'color': PAL[2 + k] if k < 2 else PAL[5 % len(PAL)]})
    ser.append({'name': '3G² (the exact threshold from 2√5 G on)', 'x': [2.1, 2 * SQ5], 'y': [3, 3], 'mode': 'line',
                'color': '#111111'})
    ser.append({'name': '4G² (the envelope bound)', 'x': [2.1, 2 * SQ5], 'y': [4, 4], 'mode': 'line', 'color': '#999999'})
    clipped = prod > ymax
    ser.append({'name': 'your point%s' % (' (height clipped at %g)' % ymax if clipped else ''), 'x': [D],
                'y': [min(prod, ymax)], 'mode': 'points', 'size': 5, 'color': K.verdict(inside)})
    plotA = K.svg_plot(ser, title='Corollary: the sufficient product P_suf against the asymmetry', xlabel='|φq − φm| / G',
                       ylabel='φqφm / G²')
    # 3D: margin prod - P_suf over (|phi_q - phi_m|, phi_q phi_m); positive = inside the region of the corollary
    Dg = _lin(2.4, 2 * SQ5 - 1e-3, 22)
    Pg = _lin(2.8, 5.0, 20)
    mcl = lambda v: max(-3.0, min(2.0, v))
    gridM = [[[x, y, mcl(y - C.psuf(x / 2))] for y in Pg] for x in Dg]
    items = [_surf(gridM, 'φqφm − P_suf(δ), clipped to [−3, 2] (red: inside the corollary)', '#1B6F8C', 0.85,
                   lambda x, y, z: K.scale(z, -3.0, 2.0, 'diverging', 0.0))]
    boundary = [[2 * x, C.psuf(x), 0.0] for x in _lin(1.2, SQ5 - 1e-3, 40) if 2.8 <= C.psuf(x) <= 5.0]
    if len(boundary) > 1:
        items.append(K.curve3(boundary, 'the boundary φqφm = P_suf(δ)', color='#111111', width=3))
    if 2.4 <= D <= 2 * SQ5 and 2.8 <= prod <= 5.0:
        items.append(K.points3([[D, prod, mcl(prod - Ps)]], 'your point', color='#111111', size=9, star=True))
        items.append(K.curve3([[D, prod, 0.0], [D, prod, mcl(prod - Ps)]], 'your margin', color='#111111', width=2, dash=True))
    plot3 = K.three_d(items, 'The margin φqφm − P_suf over (asymmetry, product); the surface crosses 0 on the boundary',
                      axes=('|φq − φm| / G', 'φqφm / G²', 'margin (G²)'),
                      colorbar=K.colorbar('φqφm − P_suf(δ): blue = outside (nothing is claimed), red = inside (every pulse has '
                                          'p + 2c < 1/2)', -3.0, 2.0, 'diverging', 0.0))
    table = K.table(['quantity (G = 1)', 'value'],
                    [['δ = |φq−φm|/2', '%.6f' % d], ['Ω = √(δ²−1)', '%.6f' % om], ['s = artanh(Ω/δ)/Ω', '%.6f' % s],
                     ['L = log(2/Ω)/s', '%.6f' % L],
                     ['term 16 − 8δ', '%.6f' % terms[0]], ['term 3 + 2ΩL + L²', '%.6f' % terms[1]],
                     ['term (δ²/Ω + L)² − δ²', '%.6f' % terms[2]], ['P_suf(δ) = max of the three', '%.6f' % Ps],
                     ['your φqφm', '%.6f' % prod], ['φqφm − P_suf', '%+.6f' % (prod - Ps)],
                     ['margin a + δ − 4  (a = (φq+φm)/2)', '%+.6f' % mg[0]],
                     ['margin (κ − Ω)s − log(2/Ω)', '%+.6f' % mg[1]],
                     ['margin (a − δ²/Ω)s − log(2/Ω)', '%+.6f' % mg[2]]])
    if inside:
        vd = ('φqφm = %.5f G² ≥ P_suf: <b>inside</b>. By the corollary every pulse of the class (fixed phase, zero detuning, '
              '0 ≤ g ≤ G, no relaxation) has p + 2c &lt; 1/2 at every duration, so r_opt = 5/12 and it is not attained.' % prod)
    elif prod >= 3:
        vd = ('φqφm = %.5f G² is below P_suf = %.5f G² (and ≥ 3G²): <b>the corollary says nothing here</b>; the threshold of '
              'this asymmetry lies in [3G², %.5f G²]%s.' % (prod, Ps, min(Ps, 4.0),
                                                              '; the envelope bound already certifies 5/12 from 4G², which your point reaches' if prod >= 4 else ''))
    else:
        vd = ('φqφm = %.5f G² &lt; 3G²: <b>outside</b>; the three margins are not the point: for a product below 3G² the '
              'resonant pulse goes below 5/12 at long durations (the long-time comparison of the paper, for δ &gt; G and '
              'Φ &gt; 4G) and the corollary is about products from 3G² upward.' % prod)
    text = ('φq = %g G, φm = %g G: |φq−φm| = %.5f G, δ = %.5f G, Ω = %.5f, s = %.5f, L = %.5f. The three terms of P_suf are '
            '%.5f, %.5f, %.5f, so <b>P_suf(δ) = %.8f G²</b> (term %s decides). %s The three scalar margins of the proof at your '
            'product, in floating point (the paper encloses them by interval arithmetic at two other points), are %+.5f, '
            '%+.5f, %+.5f: the corollary holds exactly when none is negative (here %s). Written proof, Isabelle pieces '
            'for the ingredients; the numbers above are computed here, not certified.'
            % (pq, pm, D, d, om, s, L, terms[0], terms[1], terms[2], Ps, act, vd, mg[0], mg[1], mg[2],
               'none is' if min(mg) >= 0 else 'at least one is'))
    return K.result(text, [plot3, plotA], table)

