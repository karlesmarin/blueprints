# encaje: laboratorios del blueprint robust-offset (paper B): una run_* por figura calculada del paper y dos laboratorios
# de observaciones (rem:corr, rem:relax); Python puro (Pyodide). USA Lemmario (labs [[lab]], labkit.py copiado de
# qsl-diagnostics) y su prueba de lector en navegador (labweb); catálogo mirado: ninguna ficha dibuja estas figuras ni
# integra la dinámica de dos niveles, el cálculo vive en robust_core.py.
"""Labs of «Robust qubit–memory transfer against quasi-static frequency noise costs time and exposure».

- run_disk   Figure 1 / thm:robust: design a pulse (bang-bang, turn-wait-turn, C_{pi+phi} S C_phi, or a random piecewise
             pulse with complex coupling and detuning), integrate the exact dynamics, read A, B, |zeta|, T and see
             whether the point meets the frontier T >= T0 + arccos(|zeta|/z0)/G and the disk (|zeta| - z0)^2 <= xy.
- run_cost   Figure 2 / prop:cost: cost of cancelling the leakage with fixed phase, closed form against the minimum over
             the Dubins U-turns, and the curve r(t) = int n of the optimal turn.
- run_second Figure 3 / prop:slow2, prop:noiseloss: excess of the bang-bang pulse over the square pulse in (rho, d) and
             J/J_square against Lambda (zero-leakage family, lower bound for every pulse).
- run_corr   rem:corr: the band of rho where the square pulse is optimal for correlated offsets (numerical, fixed phase).
- run_relax  rem:relax: Lambda_c(r) with relaxation of the qubit (numerical, fixed phase).
- run_unified rem:unified: the sufficient condition for both (offset correlation and relaxation), its margin and a numerical check.
All numbers are computed here; the certificates (interval arithmetic) are in the paper. Checked by comprueba_lab.py."""
import json
import math
import random

import labkit as K
import robust_core as C

ORANGE, BLUE, GREEN, GREY, RED = '#B5530F', '#1B6F8C', '#2E7D32', '#9AA7B0', '#C62828'


def _num(p, key, default, lo, hi, what):
    try:
        v = float(str(p.get(key, default)).replace(',', '.'))
    except ValueError:
        raise ValueError('%s must be a number' % what)
    if not (lo <= v <= hi):
        raise ValueError('%s must lie in [%g, %g]' % (what, lo, hi))
    return v


def _pad3(items, frames=(), f=0.35):
    """The 3D viewer of Lemmario scales the three axes by the largest extent of the data and does not keep the corners of
    the box inside the canvas: an invisible pair of points widens the box by ``f`` of its size on every side, so that
    nothing is cut at any angle (seen in the first captures of these labs)."""
    lo, hi = [float('inf')] * 3, [float('-inf')] * 3
    for lst in [items] + [list(fr) for fr in frames]:
        for it in lst:
            pts = [v for row in it['grid'] for v in row] if it['type'] == 'surface' else it['points']
            for v in pts:
                for i in range(3):
                    lo[i], hi[i] = min(lo[i], v[i]), max(hi[i], v[i])
    r = max(hi[i] - lo[i] for i in range(3)) or 1.0
    a = [lo[i] - f * r for i in range(3)]
    b = [hi[i] + f * r for i in range(3)]
    return list(items) + [K.points3([a, b], '', color='#ffffff', size=1, opacity=0.0)]


# ======================================================================= Figure 1: thm:robust
def build_pulse(kind, a, w, seed, k, umax, dmax):
    if kind == 'bangbang':
        return C.pieces_bang_bang(abs(a), rev=a < 0)
    if kind == 'twt':
        return C.pieces_twt(a, w)
    if kind == 'back':
        return C.pieces_back(a, w)
    rng = random.Random(int(seed))
    for _ in range(20):
        pl = C.random_pulse(rng, int(k), umax, dmax)
        if pl:
            return pl
    return None


def _name(kind, a, w, seed, k):
    if kind == 'bangbang':
        return 'Bang–bang pulse, d = %.4f%s' % (abs(a), ' (time reverse)' if a < 0 else '')
    if kind == 'twt':
        return 'Turn–wait–turn, α = %.4f, wait w = %.4f/G' % (a, w)
    if kind == 'back':
        return 'C_{π+φ} S C_φ (turn π+φ, wait, turn φ back), φ = %.4f, wait w = %.4f/G' % (a, w)
    return 'Random piecewise pulse (seed %d, %d pieces, complex g, detuning; the last piece closes the transfer)' % (seed, k)


def run_disk(params):
    p = json.loads(params)
    kind = str(p.get('pulse', 'bangbang')).strip().lower()
    if kind not in ('bangbang', 'twt', 'back', 'random'):
        return K.error('pulse is bangbang, twt, back or random')
    try:
        a = _num(p, 'a', 0.848, -math.pi / 2, math.pi, 'the pulse parameter a')
        w = _num(p, 'w', 0.5, 0, 20, 'the wait w (units 1/G)')
        seed = int(_num(p, 'seed', 3, 0, 10 ** 6, 'the seed'))
        k = int(_num(p, 'k', 6, 1, 12, 'the number of pieces'))
        umax = _num(p, 'umax', 1.0, 0.2, 4.0, 'the coupling bound |g|/G')
        dmax = _num(p, 'dmax', 2.0, 0, 3.0, 'the largest detuning |D|/G')
    except ValueError as e:
        return K.error(str(e))
    if kind == 'twt' and not (0 <= a <= math.pi):
        return K.error('turn-wait-turn: the angle α must lie in [0, π]')
    if kind == 'back' and not (0 <= a <= math.pi / 2):
        return K.error('C_{π+φ} S C_φ: the angle φ must lie in [0, π/2]')
    pl = build_pulse(kind, a, w, seed, k, umax, dmax)
    if pl is None:
        return K.error('could not complete the transfer with this seed; try another one')
    c = C.evolve(pl)
    z0, A0, T0 = C.Z0, C.A0, C.T0
    if c['trans'] > 1e-6:
        return K.error('this pulse does not complete the transfer (|U_aa| = %.3g): the theorem is about complete '
                       'transfers only' % c['trans'])
    ma, mb = C.margins(c)
    gmax = max(abs(g) for g, _, _ in pl)
    legal = gmax <= 1 + 1e-9
    eq_a, eq_b = abs(ma) < 1e-9, abs(mb) < 1e-9 and c['z'] <= z0
    zr = c['z'] / z0
    if not legal:
        verdict = ('This pulse uses |g| up to %.3g G: <b>outside the hypothesis |g| ≤ G</b>, so the theorem does not '
                   'apply%s.' % (gmax, ' (and the inequalities are violated: margin %.3g)' % min(ma, mb) if min(ma, mb) < -1e-9
                                 else ', although here the inequalities happen to hold'))
    elif min(ma, mb) < -1e-9:
        verdict = '<b>VIOLATES the theorem</b> (margin %.3g): this should not happen with |g| ≤ G.' % min(ma, mb)
    elif eq_a and c['z'] >= z0 - 1e-9:
        verdict = ('The point lies <b>on the disk (a) with equality</b> (margin %.1e): turn–wait–turn, equality on the '
                   'branch |ζ| ≥ z0.' % ma)
    elif eq_b:
        verdict = ('The point lies <b>on the frontier (b) with equality</b> (margin %.1e): the bang–bang pulse, the '
                   'fastest transfer with this leakage.' % mb)
    else:
        verdict = ('Inside the allowed region, with strict inequality: margin of the disk (a) %.3g, margin of the '
                   'frontier (b) %.3g.' % (ma, mb))
    text = ('%s. Integrated exactly (%d pieces, |g| ≤ %.3g G): <b>A = %.5f</b>, <b>B = %.5f</b> (A + B = T = %.5f), '
            '<b>|ζ| = %.5f</b> (|ζ|/z0 = %.4f), transfer |U<sub>aa</sub>| = %.1e. The square pulse has A = B = A0 = %.5f, '
            '|ζ| = z0 = %.2f, T0 = %.5f. Theorem (a): A − A0 = %.5f, B − A0 = %.5f, product %.5f against (|ζ| − z0)² = '
            '%.5f; theorem (b): T − T0 − %s = %.5f. %s'
            % (_name(kind, a, w, seed, k), len(pl), gmax, c['A'], c['B'], c['T'], c['z'], zr, c['trans'], A0, z0, T0,
               c['A'] - A0, c['B'] - A0, (c['A'] - A0) * (c['B'] - A0), (c['z'] - z0) ** 2,
               'arccos(|ζ|/z0)/G' if c['z'] <= z0 else '2(|ζ| − z0)', mb, verdict))
    rng = random.Random(7919 + seed)
    cloud = []
    for _ in range(150):
        q = C.random_pulse(rng, rng.randint(2, 7), umax, dmax)
        if q:
            cc = C.evolve(q)
            if cc['trans'] < 1e-6:
                cloud.append(cc)
    nviol = sum(1 for cc in cloud if min(C.margins(cc)) < -1e-9)
    text += (' Context: %d random complete transfers with |g| ≤ %.3g G (grey): %d of them violate (a) or (b)%s.'
             % (len(cloud), umax, nviol, '' if umax <= 1 else ' — the bound is exceeded on purpose'))
    zz = [i / 100 for i in range(101)]
    ze = [1 + i / 40 for i in range(25)]
    ds = [i * math.pi / 2 / 40 for i in range(41)]
    shown = [cc for cc in cloud if cc['z'] / z0 < 1.8 and cc['T'] < 6.5]
    # colour = margin to the theorem's bounds (red: violates, white: on the bound, blue: inside); your pulse: verdict
    mcol = lambda cc: K.scale(-min(C.margins(cc)), -1.5, 0.5, 'diverging', 0.0)
    ucol = K.verdict(min(ma, mb) >= -1e-9)
    series = [{'name': '%d random pulses, coloured by margin' % len(cloud), 'x': [cc['z'] / z0 for cc in shown], 'y': [cc['T'] for cc in shown],
               'color': GREY, 'colors': [mcol(cc) for cc in shown], 'size': 3},
              {'name': 'frontier T0 + arccos(|ζ|/z0)/G  (b)', 'x': zz, 'y': [T0 + math.acos(v) for v in zz], 'mode': 'line',
               'color': ORANGE},
              {'name': 'T0 + 2(|ζ| − z0)  (turn–wait–turn)', 'x': ze, 'y': [T0 + (v - 1) for v in ze], 'mode': 'line', 'color': BLUE},
              {'name': 'bang–bang family', 'x': [math.cos(d) for d in ds], 'y': [T0 + d for d in ds], 'color': ORANGE, 'size': 2.5},
              {'name': 'your pulse (green: meets the theorem, red: violates)', 'x': [zr], 'y': [c['T']], 'color': ucol, 'colors': [ucol], 'size': 8}]
    svg = K.svg_plot(series, 'Duration against leakage (units 1/G)', '|ζ| / z0', 'duration G·T', figure='paperfig-1')
    L = max(1.2, min(3.0, 1.15 * max(c['A'] - A0, c['B'] - A0)))
    n = 26
    xs = [L * i / (n - 1) for i in range(n)]
    zmax = max(1.2, 1.1 * c['z'] + 0.1)
    upper = K.surface3(lambda x, y: min(z0 + math.sqrt(x * y), zmax), xs, xs, 'sheet |ζ| = z0 + √((A−A0)(B−A0))',
                       color='#c9d6e3', opacity=0.28)
    lower = K.surface3(lambda x, y: max(z0 - math.sqrt(x * y), 0.0), xs, xs, 'sheet |ζ| = z0 − √((A−A0)(B−A0))',
                       color='#d9c9e3', opacity=0.28)
    inb = [cc for cc in cloud if cc['A'] - A0 <= L and cc['B'] - A0 <= L and cc['z'] <= zmax]
    items = [upper, lower,
             K.points3([[cc['A'] - A0, cc['B'] - A0, cc['z']] for cc in inb], 'random pulses', color='#555555', size=4,
                       colors=[mcol(cc) for cc in inb]),
             K.curve3([[(d - math.sin(d)) / 2, (d + math.sin(d)) / 2, math.cos(d) / 2] for d in ds], 'bang–bang (equality in b)',
                      color=ORANGE, width=3),
             K.curve3([[(d + math.sin(d)) / 2, (d - math.sin(d)) / 2, math.cos(d) / 2] for d in ds], '', color=ORANGE, width=3, dash=True)]
    for al, col in ((math.pi / 4, BLUE), (math.pi / 2, '#3F8FB0'), (3 * math.pi / 4, '#6AA9C4')):
        items.append(K.curve3([[ww * (1 + math.cos(al)) / 2, ww * (1 - math.cos(al)) / 2, z0 + ww * math.sin(al) / 2]
                               for ww in [L * i / 20 for i in range(21)]],
                              'turn–wait–turn (equality in a)' if al == math.pi / 4 else '', color=col, width=2.2))
    items.append(K.points3([[c['A'] - A0, c['B'] - A0, c['z']]], 'your pulse', color=ucol, size=9, star=True))
    bar = K.colorbar('margin to the bound of the theorem (dots); your pulse: green meets it, red violates it',
                     stops=[['margin +1.5 (well inside)', K.scale(-1.5, -1.5, 0.5, 'diverging', 0.0)],
                            ['0: on the bound', K.scale(0.0, -1.5, 0.5, 'diverging', 0.0)],
                            ['−0.5: violates', K.scale(0.5, -1.5, 0.5, 'diverging', 0.0)]])
    td = K.three_d(_pad3(items), 'The theorem as a disk: (A−A0, B−A0, |ζ|) between two sheets',
                   axes=('(A−A0)·G', '(B−A0)·G', '|ζ|·G'), colorbar=bar)
    return K.result(text, [td, svg])


# ======================================================================= Figure 2: prop:cost
def cost_of_s(gq, gm, s):
    """gq (A - A0) + gm (B - A0) at axial displacement s (units of z0, G = 1) with the shortest U-turn."""
    L = C.dubins_L(s)
    return 0.25 * ((gq + gm) * L + (gq - gm) * s) - (gq + gm) * math.pi / 4


def run_cost(params):
    p = json.loads(params)
    try:
        gq = _num(p, 'gq', 0.01, 1e-4, 1e4, 'γ_q/G')
        gm = _num(p, 'gm', 0.04, 1e-4, 1e4, 'γ_m/G')
    except ValueError as e:
        return K.error(str(e))
    cstar = (gq + gm) / 2 * math.acos(abs(gq - gm) / (gq + gm))
    bound = max(math.sqrt(gq * gm), math.pi / 2 * min(gq, gm))
    sstar = (gq + gm) / math.sqrt(gq * gm)
    smax = max(6.0, 1.4 * sstar)
    ss = [-smax + 2 * smax * i / 600 for i in range(601)]
    cs = [cost_of_s(gq, gm, s) for s in ss]
    i = min(range(len(ss)), key=lambda j: cs[j])
    s_num, c_num = C.golden(lambda s: cost_of_s(gq, gm, s), ss[max(i - 1, 0)], ss[min(i + 1, len(ss) - 1)])
    phi = math.acos(abs(gq - gm) / (gq + gm))
    w = 0.0 if phi > math.pi / 2 - 1e-9 else 1 / math.tan(phi)
    best = None
    for rev in (False, True):
        pl = C.pieces_back(phi, w)
        if rev:
            pl = pl[::-1]
        d = C.evolve(pl, steps=16)
        cost = gq * (d['A'] - C.A0) + gm * (d['B'] - C.A0)
        if best is None or cost < best[0]:
            best = (cost, d, rev)
    cost_dyn, d, rev = best
    eq = abs(gq - gm) < 1e-12 * (gq + gm)
    text = ('γ<sub>q</sub> = %g G, γ<sub>m</sub> = %g G. Closed form of the cost proposition:<b>C* = %.8g</b> (G = 1). Minimum over the '
            'shortest Dubins U-turns (cost as a function of the axial displacement s, searched on a grid and refined): '
            '<b>%.8g</b> at s = %.5f z0 (the proof gives |s| = (γq+γm)/√(γqγm) = %.5f, sign opposite to γq − γm); '
            'difference %.1e. The pulse that attains it (a turn of π+φ, a wait w = cot φ / G, a turn of φ back; φ = %.5f, '
            'w = %.5f%s) integrated exactly gives A = %.6f, B = %.6f, |ζ| = %.1e, |U<sub>aa</sub>| = %.1e and cost '
            '<b>%.8g</b>. Bound for every pulse (the corollary):max(√(γqγm), (π/2) min γ) = %.6g; C*/bound = %.4f%s.'
            % (gq, gm, cstar, c_num, s_num, sstar, abs(c_num - cstar), phi, w, ' — equal rates: the bang–bang pulse' if eq else '',
               d['A'], d['B'], d['z'], d['trans'], cost_dyn, bound, cstar / bound,
               ' (the bound is attained: equal rates)' if eq else ''))
    # colour = cost, one sequential scale in 2D and 3D (light = cheap, dark = expensive)
    clo, chi = min(cs), sorted(cs)[int(0.8 * len(cs))]
    ccol = lambda v: K.scale(v, clo, chi, 'sequential')
    svg = K.svg_plot([{'name': 'cost γq(A−A0) + γm(B−A0) of the shortest U-turn (colour = cost)', 'x': ss, 'y': cs, 'mode': 'line', 'color': BLUE},
                      {'name': 'cost, sampled', 'x': ss[::6], 'y': cs[::6], 'color': BLUE, 'colors': [ccol(v) for v in cs[::6]], 'size': 3.2},
                      {'name': 'bound for every pulse', 'x': [ss[0], ss[-1]], 'y': [bound, bound], 'mode': 'line', 'color': GREEN},
                      {'name': 'minimum C*', 'x': [s_num], 'y': [c_num], 'color': RED, 'size': 7}],
                     'Cost of cancelling the leakage, against the axial displacement s (units z0)', 's = (A − B)/z0',
                     'cost (units 1/G)', figure='paperfig-2')
    path = d['path']
    ghost = [K.curve3(path, 'optimal U-turn, whole', color=GREY, width=1.4, dash=True)]
    half = [[0.0, (1 - math.cos(2 * t)) / 2, math.sin(2 * t) / 2] for t in [math.pi / 2 * j / 30 for j in range(31)]]
    ghost.append(K.curve3(half, 'square pulse (open U-turn: |ζ| = z0)', color=ORANGE, width=1.6, dash=True))
    for ph in (math.pi / 3, 2 * math.pi / 3):
        ghost.append(K.curve3([[-q[1] * math.sin(ph), q[1] * math.cos(ph), q[2]] for q in path],
                              'same pulse, coupling phase turned' if ph < 2 else '', color='#c9d6e3', width=1.2))
    npt = len(path)
    idx = [round(j * (npt - 1) / 24) for j in range(1, 25)]
    frames, labels = [], []
    # running cost along the curve: A(t) = (t + r_z)/2, B(t) = (t - r_z)/2 with t = arclength (|n| = 1)
    tt = [0.0]
    for a_, b_ in zip(path[:-1], path[1:]):
        tt.append(tt[-1] + math.dist(a_, b_))
    run = [gq * ((t_ + p_[2]) / 2 - C.A0) + gm * ((t_ - p_[2]) / 2 - C.A0) for t_, p_ in zip(tt, path)]
    rlo, rhi = min(0.0, min(run)), max(run)
    rcol = lambda v: K.scale(v, rlo, rhi, 'sequential')
    for j in idx:
        frames.append([K.curve3(path[:j + 1], 'r(t) so far', color=BLUE, width=3),
                       K.points3(path[:j + 1], 'running cost', color=BLUE, size=3.5, colors=[rcol(v) for v in run[:j + 1]]),
                       K.points3([path[j]], 'now', color=RED, size=8, star=True)])
        labels.append('%.2f of %.2f' % (d['T'] * j / (npt - 1), d['T']))
    td = K.three_d(_pad3(ghost, frames), 'The curve r(t) = ∫n dt of the optimal turn: ▶ runs the time (length = duration)',
                   axes=('r_x·G', 'r_y·G (lateral)', 'r_z·G (axial)'),
                   colorbar=K.colorbar('running cost γq(A−A0)+γm(B−A0) along the turn (same scale as the 2D cost)', rlo, rhi, 'sequential'),
                   slider={'label': 'time t/G⁻¹', 'values': labels, 'items': frames, 'start': len(frames) - 1})
    return K.result(text, [td, svg])


# ======================================================================= Figure 3: prop:slow2, prop:noiseloss
A0H = C.A0H


def F_rho(rho, z, A, B):
    return 2 * (1 + rho) * z * z + A * A + rho * B * B


def excess(rho, d):
    """(F_bb - F_sq)/F_sq for the bang-bang pulse of parameter d (units G = 1/2: z0 = 1, A0 = pi/2)."""
    fb = F_rho(rho, math.cos(d), A0H + d - math.sin(d), A0H + d + math.sin(d))
    fs = F_rho(rho, 1.0, A0H, A0H)
    return (fb - fs) / fs


def best_d(rho, n=1500):
    ds = [math.pi / 2 * i / n for i in range(n + 1)]
    i = min(range(len(ds)), key=lambda j: excess(rho, ds[j]))
    return C.golden(lambda d: excess(rho, d), ds[max(i - 1, 0)], ds[min(i + 1, n)])


_SGRID = ([-2 + 4 * i / 80 for i in range(81)]
          + [-math.exp(math.log(2.0001) + i * (math.log(3000) - math.log(2.0001)) / 1200) for i in range(1201)]
          + [math.exp(math.log(2.0001) + i * (math.log(3000) - math.log(2.0001)) / 1200) for i in range(1201)])
_LGRID = [(s, C.dubins_L(s)) for s in _SGRID]


def zero_leakage_ratio(lam):
    """min over the zero-leakage pulses (z = 0, A = (L+s)/2, B = (L-s)/2, shortest U-turn) of J/J_sq, memory loss only
    (units G = 1/2, gamma_m = 1, sigma_q^2 = Lam/2): 1 + g/(12 J_sq), g = Lam Q + 4 y."""
    jsq = C.J_sq_rel(lam, 0.0)
    best = min(lam * C.q_fun(0.0, (L + s) / 2 - A0H) + 4 * ((L - s) / 2 - A0H) for s, L in _LGRID)
    return 1 + best / jsq


def lower_bound_ratio(lam):
    """The lower bound of the proof of prop:noiseloss (every pulse): minimise J over the region allowed by thm:robust,
    A, B >= A0, (a), (b) (r = 0): for each |zeta| the inner minimum over x is convex, searched by golden section."""
    jsq = C.J_sq_rel(lam, 0.0)

    def inner(z):
        S = 2 * math.acos(min(z, 1.0)) if z <= 1 else 2 * (z - 1)
        P = (z - 1) ** 2

        def h(x):
            y = max(S - x, (P / x) if x > 0 else (1e12 if P > 0 else 0.0), 0.0)
            return lam * (2 * (z * z - 1) + x * (2 * A0H + x)) + 4 * y
        return C.golden(h, 1e-9, 60.0, it=60)[1]
    zs = [1.5 * i / 100 for i in range(101)]
    vs = [inner(z) for z in zs]
    i = min(range(len(zs)), key=lambda j: vs[j])
    v = min(vs[i], C.golden(inner, zs[max(i - 1, 0)], zs[min(i + 1, 100)], it=30)[1])
    return 1 + min(v, 0.0) / jsq


def run_second(params):
    p = json.loads(params)
    try:
        rho = _num(p, 'rho', 0.1, 0, 0.5, 'ϱ = σ_m²/σ_q²')
        d = _num(p, 'd', 0.848, 0, math.pi / 2, 'the bang–bang parameter d')
        lam = _num(p, 'lam', 60, 0.5, 2000, 'Λ = σ_q²/(γ_m G)')
    except ValueError as e:
        return K.error(str(e))
    e_user = 100 * excess(rho, d)
    d_b, e_b = best_d(rho)
    lc = C.lambda_c(0.0)[0]
    zl, lb = zero_leakage_ratio(lam), lower_bound_ratio(lam)
    if lam < lc and zl >= 1 - 1e-9:
        lam_txt = 'Λ is below Λ<sub>c</sub>: no zero-leakage pulse beats the square pulse (ratio ≥ 1).'
    elif zl >= 1 - 1e-9:
        lam_txt = ('Λ is above Λ<sub>c</sub>, but this particular family (ζ = 0) has not yet caught up: the optimal member '
                   'just above Λ<sub>c</sub> has a short wait and ζ ≠ 0.')
    else:
        lam_txt = 'The zero-leakage family already beats the square pulse here.'
    text = ('Left (second-order proposition, (iii)): at ϱ = %g the bang–bang pulse with d = %g changes the second-order coefficient '
            'F = 2(1+ϱ)|ζ|² + A² + ϱB² by <b>%+.4f %%</b> relative to the square pulse (negative = better); the best d at this '
            'ϱ is %.4f with <b>%+.4f %%</b>. %s Right (memory-loss proposition, memory loss only): at Λ = %g, J/J<sub>square</sub> is '
            '<b>%.5f</b> for the best zero-leakage pulse C<sub>π+φ</sub>SC<sub>φ</sub> and the lower bound for every pulse is '
            '<b>%.5f</b>; the exact threshold for fixed phase, computed here, is Λ<sub>c</sub> = %.7f (the certified '
            'range of the paper is 7.1 to 7.92). %s'
            % (rho, d, e_user, d_b, 100 * e_b,
               ('The square pulse is already optimal among bang–bang pulses here (no d gives a negative excess).' if e_b > -1e-9
                else 'So at this ϱ the square pulse is <b>not</b> optimal.'), lam, zl, lb, lc, lam_txt))
    dg = [math.pi / 2 * i / 120 for i in range(121)]
    ser = []
    for r_, col in ((0.0, BLUE), (0.05, GREEN), (0.1264535, '#6A1B9A')):
        if abs(r_ - rho) > 1e-9:
            ser.append({'name': 'ϱ = %g' % r_, 'x': dg, 'y': [100 * excess(r_, x) for x in dg], 'mode': 'line', 'color': col})
    # colour = who wins: red = the bang–bang pulse (competitor) beats the square pulse, blue = the square pulse wins
    ecol = lambda e_pct: K.scale(-e_pct, -15.0, 22.0, 'diverging', 0.0)
    ser.append({'name': 'your ϱ = %g' % rho, 'x': dg, 'y': [100 * excess(rho, x) for x in dg], 'mode': 'line', 'color': '#222222'})
    ser.append({'name': 'your ϱ, coloured by winner', 'x': dg[::3], 'y': [100 * excess(rho, x) for x in dg[::3]],
                'color': RED, 'colors': [ecol(100 * excess(rho, x)) for x in dg[::3]], 'size': 4})
    ser.append({'name': 'best d at your ϱ', 'x': [d_b], 'y': [100 * e_b], 'color': RED, 'size': 6})
    ser.append({'name': 'your d', 'x': [d], 'y': [e_user], 'color': ORANGE, 'size': 6})
    svg1 = K.svg_plot(ser, 'Excess of the bang–bang pulse over the square pulse, in %', 'd', 'excess (%)', figure='paperfig-3')
    lams = [0.5 * math.exp(i * math.log(2000 / 0.5) / 35) for i in range(36)]
    zlv = [zero_leakage_ratio(l_) for l_ in lams]
    lbv = [lower_bound_ratio(l_) for l_ in lams]
    lg = [math.log10(l_) for l_ in lams]
    svg2 = K.svg_plot([{'name': 'square pulse', 'x': lg, 'y': [1.0] * 36, 'mode': 'line', 'color': BLUE},
                       {'name': 'zero-leakage family C(π+φ) S C(φ)', 'x': lg, 'y': zlv, 'mode': 'line', 'color': ORANGE},
                       {'name': 'family, coloured by winner', 'x': lg, 'y': zlv, 'color': ORANGE,
                        'colors': [K.scale(1 - v, -1.0, 0.45, 'diverging', 0.0) for v in zlv], 'size': 4},
                       {'name': 'lower bound, every pulse', 'x': lg, 'y': lbv, 'mode': 'line', 'color': GREEN},
                       {'name': 'your Λ (family)', 'x': [math.log10(lam)], 'y': [zl], 'color': RED, 'size': 6},
                       {'name': 'Λc (fixed phase)', 'x': [math.log10(lc)], 'y': [1.0], 'color': '#455A64', 'size': 6}],
                      'J / J_square against Λ, memory loss only', 'log10 Λ,  Λ = σq²/(γm G)', 'J / J_square')
    rr = [0.3 * i / 40 for i in range(41)]
    dd = [0.02 + 1.28 * j / 40 for j in range(41)]
    # the axes are drawn to a common scale: ϱ in 0..0.3 -> 0..10, d in 0.02..1.3 -> 0..10, excess in % -> /2.5
    X = lambda r_: r_ / 0.3 * 10
    Y = lambda d_: (d_ - 0.02) / 1.28 * 10
    Z = lambda e_: max(min(e_, 15.0), -22.0) / 2.5
    surf = K.surface3(lambda r_, d_: [X(r_), Y(d_), Z(100 * excess(r_, d_))], rr, dd, 'excess, clipped at +15 %', color='#8fb8c9', opacity=0.7,
                       colorfn=lambda x_, y_, z_: ecol(z_ * 2.5))
    zero = K.surface3(lambda x_, y_: [x_, y_, 0.0], [0, 10], [0, 10], 'zero: the square pulse', color=ORANGE, opacity=0.35)
    vals, frames = [], []
    for j in range(13):
        r_ = 0.3 * j / 12
        db, eb = best_d(r_, 400)
        vals.append('%.3f: best d = %.3f, %+.2f %%' % (r_, db, 100 * eb))
        frames.append([K.curve3([[X(r_), Y(x), Z(100 * excess(r_, x))] for x in dd], 'the slice at this ϱ', color='#000000', width=2.5),
                       K.points3([[X(r_), Y(db), Z(100 * eb)]], 'its best d', color=RED, size=8, star=True)])
    items = [surf, zero, K.points3([[X(rho), Y(d), Z(e_user)]], 'your (ϱ, d)', color=ORANGE, size=8, star=True)]
    td = K.three_d(_pad3(items, frames), 'Excess of the bang–bang pulse over the square pulse: where the surface dips below the plane it wins',
                   axes=('ϱ = σm²/σq²  (0 to 0.3)', 'd  (0.02 to 1.3)', 'excess %  (−22 to 15)'),
                   colorbar=K.colorbar('who wins at this (ϱ, d)', stops=[['−22 %: bang–bang wins clearly', ecol(-22)], ['0: tie', ecol(0)],
                                                                    ['+15 %: square pulse wins', ecol(15)]]),
                   slider={'label': 'ϱ', 'values': vals, 'items': frames,
                           'start': min(range(13), key=lambda j: abs(0.3 * j / 12 - rho))})
    return K.result(text, [td, svg1, svg2])


# ======================================================================= rem:corr
def run_corr(params):
    p = json.loads(params)
    try:
        kap = _num(p, 'kappa', 0.1, 0, 1, 'κ (correlation, 0 to 1)')
        rho = _num(p, 'rho', 0.1, 1e-3, 1e3, 'ϱ = σ_m²/σ_q²')
    except ValueError as e:
        return K.error(str(e))
    g = C.g_corr(rho, kap)
    m = C.min_family(g, both=True)
    rc = C.rho_c(kap)
    rs = C.rho_sufficient(kap)
    C_ = kap * math.sqrt(rho)
    suff_here = (math.pi / 2) * math.sqrt((1 + C_) * (rho + C_)) >= 1 + rho - 2 * C_
    rel = 100 * m['value'] / C.six_J_square(rho, kap)
    inband = rc <= rho <= 1 / rc
    mc = C.min_family(C.g_corr(rc * (1 - 1e-5), kap), ngrid=110)
    if m['value'] < -C.TOL:
        verdict = ('At (κ, ϱ) = (%g, %g) the square pulse is <b>not optimal</b>: the member φ = %.5f, w = %.5f of the family '
                   '(%s) gives 6(J − J<sub>sq</sub>) = %.5f, that is %+.3f %% of the square pulse’s coefficient.'
                   % (kap, rho, m['phi'], m['w'], 'time reversed' if m['mirror'] else 'as is', m['value'], rel))
    else:
        verdict = ('At (κ, ϱ) = (%g, %g) the square pulse is <b>optimal</b> among the pulses of fixed phase and no detuning '
                   '(numerically: min g = 0, attained by the square pulse itself).' % (kap, rho))
    text = ('Offsets with σ<sub>q</sub>² = 1, σ<sub>m</sub>² = ϱ, correlation κ (C = κσ<sub>q</sub>σ<sub>m</sub>). %s Band, computed here by '
            'bisection on the sign of min g: the square pulse is optimal exactly for ϱ in [ϱ<sub>c</sub>, 1/ϱ<sub>c</sub>] = '
            '[<b>%.10g</b>, %.5g] (your ϱ is %s). The competitor at the threshold has φ = %.5f, w = %.2e (%s). '
            'Sufficient condition of the remark, (π/2)√((σq²+C)(σm²+C)) ≥ σq²+σm²−2C: %s%s. '
            'The paper proves, for pulses of any phase and detuning, that the band can only widen as κ grows '
            '(ϱ<sub>c</sub> non-increasing); the table below shows it, and how far the sufficient condition is from it. '
            '<i>This lab is numerical (grid and golden section over the family, no interval arithmetic); the certificates '
            'are in the paper.</i>'
            % (verdict, rc, 1 / rc, 'inside the band' if inband else 'outside the band', mc['phi'], mc['w'],
               'pure bang–bang' if mc['w'] < 1e-5 else 'a wait of positive length',
               'it holds at your point' if suff_here else 'it does not hold at your point',
               ('; its lower end is ϱ = %.5g (the band is wider by a factor %.1f)' % (rs, rs / rc)) if rs else
               '; it holds for no ϱ ≤ 1 at this κ (needs κ ≥ (4−π)/(4+π) = %.5f)' % C.kappa_c_square()))
    kk = [i / 10 for i in range(11)]
    if all(abs(kap - x) > 1e-9 for x in kk):
        kk = sorted(kk + [kap])
    rcs = [rc if abs(x - kap) < 1e-12 else C.rho_c(x) for x in kk]
    kv = [x for x in kk if C.rho_sufficient(x)]
    svg = K.svg_plot([{'name': 'ϱc(κ): optimal above it', 'x': kk, 'y': [math.log10(v) for v in rcs], 'mode': 'line', 'color': BLUE},
                      {'name': 'sufficient condition (lower end)', 'x': kv, 'y': [math.log10(C.rho_sufficient(x)) for x in kv], 'mode': 'line', 'color': GREEN},
                      {'name': 'your (κ, ϱ): green = square optimal, red = competitor wins', 'x': [kap], 'y': [math.log10(min(rho, 1 / rho))],
                       'color': K.verdict(m['value'] >= -C.TOL), 'colors': [K.verdict(m['value'] >= -C.TOL)], 'size': 8}],
                     'Where the square pulse stops being optimal (σq² = 1, σm² = ϱ ≤ 1; symmetric under ϱ → 1/ϱ)', 'κ', 'log10 ϱ')
    ks = [i / 8 for i in range(9)]
    ls = [-3 + 3 * j / 15 for j in range(16)]
    grid = []
    for kk_ in ks:
        row = []
        for lg in ls:
            v = C.min_family(C.g_corr(10 ** lg, kk_), ngrid=90)['value']
            row.append([kk_ * 10, (lg + 3) / 3 * 10, max(v, -0.8) * 12])      # drawn to a common scale (see the axis labels)
        grid.append(row)
    # colour = who wins: green where min g = 0 (the square pulse is optimal), white to red as the competitor gains
    gcol = lambda z_: K.verdict(True) if z_ >= -0.024 else K.scale(-z_ / 12, -0.3, 0.8, 'diverging', 0.0)
    surf = K.surface3(lambda i, j: grid[i][j], range(len(ks)), range(len(ls)), 'min g over the family', color='#8fb8c9',
                      opacity=0.7, colorfn=lambda x_, y_, z_: gcol(z_))
    plane = K.surface3(lambda a, b: [a, b, 0.0], [0, 10], [0, 10], 'zero: the square pulse', color=ORANGE, opacity=0.3)
    edge = K.curve3([[x * 10, (math.log10(r_) + 3) / 3 * 10, 0.0] for x, r_ in zip(kk, rcs)], 'ϱc(κ): the edge of the band', color='#000000', width=3)
    rm = min(rho, 1 / rho)
    mm = C.min_family(C.g_corr(rm, kap), ngrid=90)['value']
    td = K.three_d(_pad3([surf, plane, edge, K.points3([[kap * 10, (math.log10(rm) + 3) / 3 * 10, max(mm, -0.8) * 12]], 'your point', color=RED, size=9, star=True)]),
                   'min g over (κ, ϱ): flat on the band (square pulse optimal), below the plane outside it',
                   axes=('κ  (0 to 1)', 'log10 ϱ  (−3 to 0; ϱ ≤ 1)', 'min g  (−0.8 to 0)'),
                   colorbar=K.colorbar('who wins', stops=[['green: the square pulse is optimal (min g = 0)', K.verdict(True)],
                                                          ['white: the competitor just wins', gcol(-0.3)],
                                                          ['red: the competitor wins clearly (min g ≈ −0.8)', gcol(-9.6)]]))
    return K.result(text, [td, svg], table=K.table(
        ['κ', 'ϱc(κ)', '1/ϱc', 'ϱ_suf (sufficient condition)', 'ϱ_suf / ϱc'],
        [['%g' % x, '%.8g' % r_, '%.5g' % (1 / r_), ('%.4g' % C.rho_sufficient(x)) if C.rho_sufficient(x) else 'never',
          ('%.3f' % (C.rho_sufficient(x) / r_)) if C.rho_sufficient(x) else '—']
         for x, r_ in zip(kk, rcs)]))


# ======================================================================= rem:relax
def run_relax(params):
    p = json.loads(params)
    try:
        r = _num(p, 'r', 1, 0, 1000, 'r = γ_q/γ_m')
        lam = _num(p, 'lam', 9, 0.1, 400, 'Λ = σ_q²/(γ_m G)')
    except ValueError as e:
        return K.error(str(e))
    lc, phi_c, w_c, z_c, _mir = C.lambda_c(r)
    suf = C.suficiente(r)
    m = C.min_family(C.g_loss(lam, r), both=True)
    rel = 100 * m['value'] / C.J_sq_rel(lam, r)
    if m['value'] < -C.TOL:
        verdict = ('At Λ = %g the square pulse is <b>not optimal</b>: the member φ = %.5f, w = %.5f (|ζ|/z0 = %.4f) lowers J '
                   'by %.4f %%.' % (lam, m['phi'], m['w'], m['z'], -rel))
    else:
        verdict = 'At Λ = %g the square pulse is <b>optimal</b> among the pulses of fixed phase and no detuning (numerically).' % lam
    below = C.min_family(C.g_loss(lc * (1 - 1e-6), r), both=True)['value']
    above = C.min_family(C.g_loss(lc * (1 + 1e-4), r), both=True)['value']
    text = ('Memory decay γ<sub>m</sub>, qubit relaxation γ<sub>q</sub> = rγ<sub>m</sub> (r = %g), slow noise on the qubit '
            '(Λ = σq²/(γmG)): g = 12(J − J<sub>sq</sub>) = ΛQ + 4(y + r x) over the family C(π+φ)SC(φ) (units G = 1/2). %s '
            'Threshold, computed here (g is linear in Λ, so Λ<sub>c</sub> = min of 4(y+rx)/(−Q), by Dinkelbach iterations): '
            '<b>Λ<sub>c</sub>(%g) = %.9g</b>, reached at φ = %.6f, w = %.6f, |ζ|/z0 = %.5f (so it is not a zero-leakage '
            'pulse). Just below it min g = %.1e (≥ 0 up to the tolerance), just above %.2e (< 0). Sufficient condition of '
            'the remark, (π + √(π²+16r))/2 = %.6f: the threshold is %.3f above it. The paper proves (given the planar '
            'bound) Λ<sub>c</sub>(r) = 2√r + π/2 + 4/√3 + O(r<sup>−1/2</sup>); here 2√r + π/2 + 4/√3 = %.4f, so '
            '√r·(Λ<sub>c</sub> − that) = %s (it stays bounded, about 3.8 for large r). Λ<sub>c</sub> is also proved '
            'non-decreasing and concave in r. <i>Numerical lab; the certificates and the proof are in the paper.</i>'
            % (r, verdict, r, lc, phi_c, w_c, z_c, below, above, suf, lc - suf,
               2 * math.sqrt(r) + math.pi / 2 + 4 / math.sqrt(3),
               ('%.3f' % (math.sqrt(r) * (lc - 2 * math.sqrt(r) - math.pi / 2 - 4 / math.sqrt(3)))) if r > 0 else '—'))
    rs = sorted({0, 0.1, 0.3, 1, 3, 10, 30, 100, 300, 1000, r})
    lcs = {x: (lc if x == r else C.lambda_c(x)[0]) for x in rs}
    lx = [math.log10(1 + x) for x in rs]
    svg = K.svg_plot([{'name': 'Λc(r), fixed phase (numerical)', 'x': lx, 'y': [lcs[x] for x in rs], 'mode': 'line', 'color': BLUE},
                      {'name': 'sufficient condition (π + √(π²+16r))/2', 'x': lx, 'y': [C.suficiente(x) for x in rs], 'mode': 'line', 'color': GREEN},
                      {'name': 'your (r, Λ): green = square optimal, red = competitor wins', 'x': [math.log10(1 + r)], 'y': [lam],
                       'color': K.verdict(m['value'] >= -C.TOL), 'colors': [K.verdict(m['value'] >= -C.TOL)], 'size': 8}],
                     'Threshold Λc against the qubit relaxation r = γq/γm: below the curve the square pulse is optimal',
                     'log10(1 + r)', 'Λ = σq²/(γm G)')
    rvals = [0, 1, 10, 100, 1000]
    phis = [C.A0H * (j + 0.5) / 36 for j in range(36)]
    xs = [0.2 + 2.8 * i / 22 for i in range(23)]
    frames, labels = [], []
    for rv in rvals:
        lcv = lc if rv == r else C.lambda_c(rv)[0]
        grid = []
        for xr in xs:
            lm = xr * lcv
            gg = C.g_loss(lm, rv)
            js = C.J_sq_rel(lm, rv)
            # drawn to a common scale: Λ/Λc in 0.2..3 -> 0..10, φ in 0..π/2 -> 0..10, the change in % over 6
            grid.append([[(xr - 0.2) / 2.8 * 10, ph / C.A0H * 10, max(100 * C._min_over_w(gg, ph, False)[0] / js, -60.0) / 6] for ph in phis])
        # colour = who wins: white at 0 (tie), red where the competitor lowers J (down to -60 %), blue where the square pulse is better
        frames.append([K.surface3(lambda i, j: grid[i][j], range(len(xs)), range(len(phis)), 'min over the wait of 100·(J − Jsq)/Jsq',
                                  color='#8fb8c9', opacity=0.7, colorfn=lambda x_, y_, z_: K.scale(-6 * z_, -20.0, 60.0, 'diverging', 0.0))])
        labels.append('%g  (Λc = %.3f)' % (rv, lcv))
    plane = K.surface3(lambda a, b: [a, b, 0.0], [0, 10], [0, 10], 'zero: the square pulse', color=ORANGE, opacity=0.3)
    wall = K.curve3([[(1.0 - 0.2) / 2.8 * 10, ph, 0.0] for ph in [10 * j / 30 for j in range(31)]], 'Λ = Λc', color='#000000', width=3)
    td = K.three_d(_pad3([plane, wall], frames), 'J against the square pulse over (Λ/Λc, φ): the valley opens at Λc',
                   axes=('Λ / Λc(r)  (0.2 to 3)', 'φ  (0 to π/2)', 'change of J %  (0 to −60)'),
                   colorbar=K.colorbar('who wins', stops=[['blue: the square pulse is better', K.scale(-20.0, -20.0, 60.0, 'diverging', 0.0)],
                                                          ['white: tie (change 0)', K.scale(0.0, -20.0, 60.0, 'diverging', 0.0)],
                                                          ['red: the competitor lowers J (−60 %)', K.scale(60.0, -20.0, 60.0, 'diverging', 0.0)]]),
                   slider={'label': 'r', 'values': labels, 'items': frames, 'start': 0})
    return K.result(text, [td, svg])


# ======================================================================= rem:unified
def unified_parts(sq, sm, kap, gq, gm, G):
    """Pieces of the condition of rem:unified. sq, sm = sigma_q^2, sigma_m^2; C = kap sigma_q sigma_m.
    Returns V, C, a, b, lhs = V z0, rhs = sqrt(ab), the margin rhs - lhs and the normalised margin in [-1, 1]."""
    A0, z0 = math.pi / (4 * G), 1 / (2 * G)
    C_ = kap * math.sqrt(sq * sm)
    V = max(0.0, sq + sm - 2 * C_)       # V >= 0 always (C <= sigma_q sigma_m); guards rounding only
    a, b = (sq + C_) * A0 + gq, (sm + C_) * A0 + gm
    lhs, rhs = V * z0, math.sqrt(a * b)
    den = lhs + rhs
    return {'V': V, 'C': C_, 'a': a, 'b': b, 'lhs': lhs, 'rhs': rhs, 'margin': rhs - lhs,
            'norm': (rhs - lhs) / den if den > 0 else 0.0, 'A0': A0, 'z0': z0}


def unified_delta6(x, y, u, sq, sm, C_, gq, gm, G):
    """6(J - J_sq) at the point (x, y, u) = (A - A0, B - A0, |zeta|) of the leading-order error of rem:unified."""
    A0, z0 = math.pi / (4 * G), 1 / (2 * G)
    V = sq + sm - 2 * C_
    A, B = A0 + x, A0 + y
    J = 2 * V * u * u + sq * A * A + 2 * C_ * A * B + sm * B * B + 2 * (gq * A + gm * B)
    Jsq = 2 * V * z0 * z0 + (sq + 2 * C_ + sm) * A0 * A0 + 2 * (gq + gm) * A0
    return J - Jsq


def unified_sample_min(sq, sm, C_, gq, gm, G, n=4000, seed=13):
    """Minimum of 6(J - J_sq) over n points (u, x, y) of the region the disk of thm:robust(a) allows:
    x, y >= 0, u = |zeta| in [0, 2 z0], (z0 - u)^2 <= x y when u <= z0 (half of the points on the edge of the disk)."""
    rng = random.Random(seed)
    z0 = 1 / (2 * G)
    best, arg = float('inf'), None
    for _ in range(n):
        u = rng.uniform(0, 2 * z0)
        x = rng.expovariate(1.0) * 0.5 / G + 1e-12
        ymin = (z0 - u) ** 2 / x if u <= z0 else 0.0
        y = ymin + (rng.expovariate(1.0) * 0.2 / G if rng.random() < 0.5 else 0.0)
        v = unified_delta6(x, y, u, sq, sm, C_, gq, gm, G)
        if v < best:
            best, arg = v, (x, y, u)
    return best, arg


def run_unified(params):
    p = json.loads(params)
    try:
        sq = _num(p, 'sq', 1, 0, 1e6, 'σ_q² (qubit offset variance)')
        sm = _num(p, 'sm', 0.05, 0, 1e6, 'σ_m² (memory offset variance)')
        kap = _num(p, 'kappa', 0.2, 0, 1, 'κ (correlation, 0 to 1)')
        gq = _num(p, 'gq', 0, 0, 1e6, 'γ_q (qubit relaxation rate)')
        gm = _num(p, 'gm', 0, 0, 1e6, 'γ_m (memory relaxation rate)')
        G = _num(p, 'G', 0.5, 1e-3, 1e3, 'G (coupling bound)')
        d = _num(p, 'd', 0.8, 0, math.pi / 2, 'd (bang–bang parameter, 0 to π/2)')
    except ValueError as e:
        return K.error(str(e))
    if kap > 0 and (sq == 0 or sm == 0):
        return K.error('κ > 0 needs σ_q² > 0 and σ_m² > 0 (C = κσ_qσ_m is zero if one offset vanishes): set κ = 0 or give both variances')
    P = unified_parts(sq, sm, kap, gq, gm, G)
    C_, V, A0, z0 = P['C'], P['V'], P['A0'], P['z0']
    holds = P['margin'] >= -1e-12 * max(1.0, P['rhs'])
    eps = 1e-12
    tags = []
    if sq + sm == 0 and gq + gm == 0:
        tags.append('all zero: the condition holds trivially and every pulse has zero leading-order cost')
    elif gq == 0 and gm == 0 and C_ == 0 and sq + sm > 0:
        tags.append('γ<sub>q</sub> = γ<sub>m</sub> = C = 0 with σ<sub>q</sub>² + σ<sub>m</sub>² > 0: the condition cannot hold '
                    '(π/2 √(σq²σm²) &lt; σq² + σm²), in agreement with the bang–bang pulse beating the square pulse outside [ϱ<sub>c</sub>, 1/ϱ<sub>c</sub>]')
    if gq == 0 and gm == 0 and sq + sm > 0:
        tags.append('no relaxation: it is the condition of the remark on correlated offsets, (π/2)√((σq²+C)(σm²+C)) ≥ σq²+σm²−2C (%s)'
                    % ('holds' if (math.pi / 2) * math.sqrt((sq + C_) * (sm + C_)) >= sq + sm - 2 * C_ - 1e-12 else 'fails'))
    if sm == 0 and sq > 0 and gm > 0:
        lam, rr = sq / (gm * G), gq / gm
        tags.append('σ<sub>m</sub> = C = 0: it is the condition of the remark on relaxation, Λ = σq²/(γmG) = %.5g ≤ (π + √(π² + 16r))/2 = %.5g with r = γq/γm = %.5g'
                    % (lam, C.suficiente(rr) if hasattr(C, 'suficiente') else float('nan'), rr))
    elif sm == 0 and sq > 0 and gm == 0:
        tags.append('σ<sub>m</sub> = C = 0 and γ<sub>m</sub> = 0: the right side is 0 while V z<sub>0</sub> = σq² z<sub>0</sub> &gt; 0, so it cannot hold')
    special = ('Special cases that apply: ' + '; '.join(tags) + '.') if tags else 'No special case of the remark applies (both offsets or a relaxation make it a genuine mixture).'
    # the condition, with its margin
    if holds:
        cond = ('The condition <b>holds</b>: V z<sub>0</sub> = %.6g ≤ √(ab) = %.6g, margin √(ab) − V z<sub>0</sub> = <b>%.6g</b> '
                '(ratio √(ab)/(V z<sub>0</sub>) = %s). So the square pulse minimises the leading-order error over <i>all</i> pulses (proved in the paper).'
                % (P['lhs'], P['rhs'], P['margin'], ('%.4f' % (P['rhs'] / P['lhs'])) if P['lhs'] > 0 else '∞, V = 0'))
    else:
        cond = ('The condition <b>does not hold</b>: V z<sub>0</sub> = %.6g &gt; √(ab) = %.6g, shortfall %.6g. It is only <i>sufficient</i>: '
                'the square pulse may still be optimal (the exact band is wider), but this condition no longer proves it.'
                % (P['lhs'], P['rhs'], -P['margin']))
    # smallest correlation that makes it hold
    def _m(k):
        return unified_parts(sq, sm, k, gq, gm, G)['margin']
    if sq > 0 and sm > 0:
        if _m(0.0) >= 0:
            kc = '0 (it holds already uncorrelated)'
        elif _m(1.0) < 0:
            kc = 'none in [0, 1]'
        else:
            lo, hi = 0.0, 1.0
            for _ in range(60):
                mid = (lo + hi) / 2
                if _m(mid) >= 0:
                    hi = mid
                else:
                    lo = mid
            kc = '%.6f' % hi
        kline = ' With these variances and rates, the smallest κ at which the condition holds is %s (the margin is non-decreasing in κ).' % kc
    else:
        kline = ''
    # numerical check over the region of the disk
    Cc = C_
    mn, arg = unified_sample_min(sq, sm, Cc, gq, gm, G)
    scale = max(1.0, abs(P['rhs']), P['lhs'])
    if mn >= -1e-9 * scale:
        chk = ('Numerical check: over 4000 complete transfers sampled in the region the disk (|ζ| − z<sub>0</sub>)² ≤ (A−A<sub>0</sub>)(B−A<sub>0</sub>), '
               'A, B ≥ A<sub>0</sub> allows (half of them on its edge), min 6(J − J<sub>sq</sub>) = <b>%.4g ≥ 0</b>%s.'
               % (mn, '' if holds else ' — the condition does not hold here, but the minimum may still be ≥ 0: it is only sufficient'))
    else:
        chk = ('Numerical check: over 4000 complete transfers sampled in the region the disk allows, min 6(J − J<sub>sq</sub>) = <b>%.4g &lt; 0</b> '
               'at (x, y, |ζ|) = (%.4g, %.4g, %.4g): the square pulse is beaten there%s.'
               % (mn, arg[0], arg[1], arg[2], ' — this contradicts the proof, so it would be a bug' if holds else ', as expected since the condition fails'))
    # the bang-bang pulse of the reader
    xb, yb, ub = (d - math.sin(d)) / (2 * G), (d + math.sin(d)) / (2 * G), math.cos(d) / (2 * G)
    db = unified_delta6(xb, yb, ub, sq, sm, Cc, gq, gm, G)
    bb = ('The bang–bang pulse of parameter d = %g (x = %.4g, y = %.4g, |ζ| = %.4g, exact formulas): 6(J − J<sub>sq</sub>) = <b>%.6g</b>, %s.'
          % (d, xb, yb, ub, db, 'it beats the square pulse' if db < -1e-12 else 'it does not beat the square pulse'))
    text = ('Leading-order error 6J = 2V|ζ|² + σq²A² + 2CAB + σm²B² + 2(γqA + γmB), with σq² = %g, σm² = %g, C = κσqσm = %.6g (κ = %g), '
            'V = σq² + σm² − 2C = %.6g, γq = %g, γm = %g, G = %g (z<sub>0</sub> = 1/(2G) = %.5g, A<sub>0</sub> = π/(4G) = %.5g). '
            'a = (σq²+C)A<sub>0</sub> + γq = %.6g, b = (σm²+C)A<sub>0</sub> + γm = %.6g. %s%s %s %s %s '
            '<i>What is computed and what is proved: the condition and its margin are evaluated here exactly (closed form); the sampling and the '
            'bang–bang pulse are numerical evidence only. That the square pulse is optimal whenever the condition holds is a written proof '
            '(the disk of the main theorem, part (a), and AM–GM) and is formalised in Isabelle (Square_Unified_Condition.square_unified).</i>'
            % (sq, sm, C_, kap, V, gq, gm, G, z0, A0, P['a'], P['b'], cond, kline, special, chk, bb))
    kk = [i / 40 for i in range(41)]
    if all(abs(kap - x) > 1e-9 for x in kk):
        kk = sorted(kk + [kap])
    ys = [unified_parts(sq, sm, x, gq, gm, G)['norm'] for x in kk]
    pcol = K.verdict(holds)
    svg = K.svg_plot([{'name': 'normalised margin (√ab − Vz0)/(√ab + Vz0) against κ', 'x': kk, 'y': ys, 'mode': 'line', 'color': BLUE},
                      {'name': 'zero: the condition is tight', 'x': [0, 1], 'y': [0, 0], 'mode': 'line', 'color': GREY},
                      {'name': 'your κ: green = condition holds, red = it fails', 'x': [kap], 'y': [P['norm']], 'color': pcol, 'colors': [pcol], 'size': 8}],
                     'Margin of the sufficient condition against the correlation κ (your σ², γ, G fixed): above zero the square pulse is optimal for all pulses',
                     'κ', 'normalised margin')
    # 3D: normalised margin over (kappa, log10 rho), sigma_q^2 fixed
    s0 = sq if sq > 0 else 1.0
    ks = [i / 8 for i in range(9)]
    ls = [-3 + 6 * j / 16 for j in range(17)]
    grid = [[[k_ * 10, (lg + 3) / 6 * 10, unified_parts(s0, s0 * 10 ** lg, k_, gq, gm, G)['norm'] * 10] for lg in ls] for k_ in ks]
    surf = K.surface3(lambda i, j: grid[i][j], range(len(ks)), range(len(ls)), 'normalised margin', color='#8fb8c9', opacity=0.7,
                      colorfn=lambda x_, y_, z_: K.verdict(z_ >= -1e-9))
    plane = K.surface3(lambda a_, b_: [a_, b_, 0.0], [0, 10], [0, 10], 'zero: the condition is tight', color=ORANGE, opacity=0.3)
    lgr = math.log10(sm / sq) if sq > 0 and sm > 0 else (-3.0 if sm == 0 else 3.0)
    lgr = max(-3.0, min(3.0, lgr))
    pt = K.points3([[kap * 10, (lgr + 3) / 6 * 10, P['norm'] * 10]], 'your point', color=RED, size=9, star=True)
    td = K.three_d(_pad3([surf, plane, pt]),
                   'Normalised margin over (κ, log10 ϱ), with σq² and the rates fixed: green above the zero plane (condition holds), red below',
                   axes=('κ  (0 to 1)', 'log10 ϱ, ϱ = σm²/σq²  (−3 to 3)', 'normalised margin  (−1 to 1)'),
                   colorbar=K.colorbar('condition', stops=[['green: it holds (margin ≥ 0)', K.verdict(True)],
                                                           ['red: it fails (margin < 0)', K.verdict(False)]]))
    rows = [['σq²', '%g' % sq], ['σm²', '%g' % sm], ['C', '%.6g' % C_], ['V', '%.6g' % V], ['a', '%.6g' % P['a']], ['b', '%.6g' % P['b']],
            ['V z0', '%.6g' % P['lhs']], ['√(ab)', '%.6g' % P['rhs']], ['margin', '%.6g' % P['margin']],
            ['min 6(J − J_sq) over 4000 samples', '%.6g' % mn], ['6(J − J_sq), bang–bang d = %g' % d, '%.6g' % db]]
    return K.result(text, [td, svg], table=K.table(['quantity', 'value'], rows))
