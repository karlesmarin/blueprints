# encaje: laboratorio del blueprint prescribed-moments-II: las figuras 3D (una por figura del paper, pensada para ella).
"""3D companions of the seven labs (Carles, 10-nov: «no hay fig 3d, modernas y espectaculares»).

Each figure is built for its own figure of the paper, from the same computation as the 2D one:
  grid      the classification as a skyline: dead cells flat, live cells standing, the column n = 3 rising with deg Q_k
  collapse  m on a helix of period 6: the gcd(m, 6) classes become vertical lines, and so does S_m
  genus     two ribbons (the witnesses) under the arithmetic genus: the gap is what the nodes cannot pay
  values    stems: each value of 6C/(p-1) at height = its share of primes; ▶ adds primes and the shares settle
  degree    a cone: k turns around the axis with period 6, deg Q_k is the height: six straight ladders, one lower
  primes    Sato–Tate tower: each prime at the angle θ_p of its trace a_p = 2√p cos θ_p, rising with p; purple where
            the cubic splits; ▶ grows the tower
  circle    the curve (θ, s_k(θ), log u(θ)) in space, with its roots; ▶ runs k
The engine (lemmario lab3d.js) uses one scale for the three axes: every figure is normalised to about [0, 2]."""
import math

import moments_lab as L

GR = '#B9C0C7'


def grid3d(kmax, nmax):
    items, dead = [], []
    top = max(1 + len(L.Qk(k)[0]) - 1 for k in range(3, kmax + 1))
    sx, sy, sz = 2.0 / max(1, nmax - 3), 2.0 / max(1, kmax - 3), 1.4 / top
    for k in range(3, kmax + 1):
        deg = len(L.Qk(k)[0]) - 1
        for n in range(3, nmax + 1):
            x, y = (n - 3) * sx, (k - 3) * sy
            if not L.artin_tate(k, n):
                dead.append([x, y, 0])
                continue
            if n > 3 or deg == 0:
                h, col, nm = 1.0, L.VERDE, 'Artin–Tate, quadratic characters'
            else:
                h, col, nm = 1.0 + deg, (L.MORADO if k in (6, 9) else '#5E7F5C'), 'n = 3, nonabelian: height 1 + deg Q_k'
            items.append({'type': 'curve', 'points': [[x, y, 0], [x, y, h * sz]], 'color': col, 'width': 9, 'name': nm})
            items.append({'type': 'points', 'points': [[x, y, h * sz]], 'color': col, 'size': 5})
    items.append({'type': 'points', 'points': dead, 'color': GR, 'size': 2.5, 'name': 'not Artin–Tate'})
    seen, out = set(), []
    for it in items:  # one legend entry per name
        if it.get('name') in seen:
            it = dict(it)
            it.pop('name')
        elif it.get('name'):
            seen.add(it['name'])
        out.append(it)
    return {'kind': '3d', 'title': 'The classification as a skyline: everything flat except the column n = 3, which '
                                   'rises with deg Q_k (one cubic fibre per root), and three cells at k = 3, 5',
            'axes': ['n', 'k', 'height'], 'items': out}


def collapse3d(rows, mmax):
    col = {1: L.SUAVE, 2: L.AZUL, 3: L.MORADO, 6: L.NARANJA}
    name = {1: 'gcd 1: S_m = {3}', 2: 'gcd 2: {3,4,6}', 3: 'gcd 3: {3} (same as gcd 1)', 6: 'gcd 6: {3,4,5,6}'}
    pts = {g: [] for g in col}

    def at(m, r=1.0):
        a = 2 * math.pi * m / 6.0
        return [1 + r * math.cos(a), 1 + r * math.sin(a), 2.0 * m / max(1, mmax)]

    for row in rows:
        m, g, s = row[0], row[2], row[3]
        size = 3 + 1.6 * (s.count(',') + 1)
        pts[g].append((at(m), size))
    items = [{'type': 'curve', 'points': [at(t / 20.0) for t in range(0, 20 * mmax + 1)], 'color': '#D9DDE1',
              'width': 1.2, 'name': 'm = 1, 2, 3, … on a helix of period 6'}]
    for g in (1, 3, 2, 6):
        if not pts[g]:
            continue
        for j, (p, size) in enumerate(pts[g]):
            it = {'type': 'points', 'points': [p], 'color': col[g], 'size': size}
            if j == 0:
                it['name'] = name[g]
            items.append(it)
        for r in range(6):  # the vertical line of each residue class r mod 6 in this gcd class
            if math.gcd(r, 6) == g or (r == 0 and g == 6):
                ms = [m for m in range(1, mmax + 1) if m % 6 == r]
                if len(ms) > 1:
                    items.append({'type': 'curve', 'points': [at(ms[0]), at(ms[-1])], 'color': col[g], 'width': 1.4,
                                  'dash': True})
    return {'kind': '3d', 'title': 'm on a helix of period 6 (marker size = |S_m|): each gcd class is a set of vertical '
                                   'lines, so S_m is decided by m mod 6, and gcd 1 and gcd 3 give the same answer',
            'axes': ['', '', 'm'], 'items': items}


def genus3d(KS, g4, g6):
    top = max(max(g6), 1)
    sx, sz = 2.0 / max(1, len(KS) - 1), 1.5 / top
    pa = [(k - 1) * (k - 2) // 2 for k in KS]

    def ribbon(vals, y0, w=0.28):
        return [[[i * sx, y, v * sz] for y in (y0, y0 + w)] for i, v in enumerate(vals)]
    items = [{'type': 'surface', 'grid': ribbon(g4, 0.0), 'color': L.AZUL, 'opacity': 0.55,
              'name': 'genus of the n = 4 witness (1,1,1,1)'},
             {'type': 'surface', 'grid': ribbon(g6, 0.7), 'color': L.MORADO, 'opacity': 0.55,
              'name': 'genus of the n = 6 witness (3,1,1,1)'},
             {'type': 'curve', 'points': [[i * sx, 0.14, v * sz] for i, v in enumerate(pa)], 'color': L.NARANJA,
              'width': 2, 'dash': True, 'name': 'arithmetic genus (k−1)(k−2)/2'},
             {'type': 'curve', 'points': [[i * sx, 0.84, v * sz] for i, v in enumerate(pa)], 'color': L.NARANJA,
              'width': 2, 'dash': True}]
    zeros = [[i * sx, 0.14, 0] for i, v in enumerate(g4) if v == 0] + [[i * sx, 0.84, 0] for i, v in enumerate(g6) if v == 0]
    if zeros:
        items.append({'type': 'points', 'points': zeros, 'color': L.VERDE, 'marker': 'star', 'size': 10,
                      'name': 'genus 0: a rational witness (k = 3, 5)'})
    return {'kind': '3d', 'title': 'Two ribbons under the arithmetic genus: past k = 5 neither touches zero, so no '
                                   'witness is rational and the cell dies', 'axes': ['k', 'witness', 'genus'],
            'items': items}


def values3d(KS, pmax):
    PS = L.primes(5, pmax)
    vals = {k: [(q, L.values_n3(k, q)) for q in PS if k % q] for k in KS}
    top = max(v for k in KS for _, v in vals[k]) or 1
    sx, sy = 2.0 / max(1, len(KS) - 1), 2.0 / top
    cuts = sorted(set([PS[min(len(PS) - 1, int(len(PS) * f))] for f in (0.1, 0.2, 0.3, 0.45, 0.6, 0.8, 1.0)]))
    frames = []
    for c in cuts:
        its = []
        for i, k in enumerate(KS):
            vs = [v for q, v in vals[k] if q <= c]
            if not vs:
                continue
            col = L.VERDE if L.Qk(k)[0] == [1] else L.AZUL
            for v in sorted(set(vs)):
                sh = vs.count(v) / float(len(vs))
                its.append({'type': 'curve', 'points': [[i * sx, v * sy, 0], [i * sx, v * sy, 1.6 * sh]],
                            'color': col, 'width': 5})
                its.append({'type': 'points', 'points': [[i * sx, v * sy, 1.6 * sh]], 'color': col, 'size': 4})
        frames.append(its)
    base = [{'type': 'points', 'points': [[0, 0, 0]], 'color': L.VERDE, 'size': 0.1, 'name': 'Q_k constant'},
            {'type': 'points', 'points': [[0, 0, 0]], 'color': L.AZUL, 'size': 0.1, 'name': 'Q_k has a root'}]
    return {'kind': '3d', 'title': 'Each value of 6C_k(3,p)/(p−1) as a stem, its height the share of primes giving '
                                   'it: ▶ adds primes and the shares settle (Chebotarev)',
            'axes': ['k', 'value', 'share'], 'items': base,
            'slider': {'label': 'primes up to', 'values': cuts, 'items': frames}}


def degree3d(kmax):
    G = {k: len(L.Qk(k)[0]) - 1 for k in range(3, kmax + 1)}
    top = max(G.values()) or 1

    def at(k):
        a = 2 * math.pi * k / 6.0
        r = 0.15 + 0.85 * k / float(kmax)
        return [1 + r * math.cos(a), 1 + r * math.sin(a), 2.0 * G[k] / top]
    items = []
    for r in range(6):
        ks = [k for k in G if k % 6 == r]
        col = L.NARANJA if r == 1 else L.AZUL
        items.append({'type': 'curve', 'points': [at(k) for k in ks], 'color': col, 'width': 2.2,
                      'name': ('k ≡ 1 mod 6: one step lower' if r == 1 else
                               ('k ≡ 0, 2, 3, 4, 5 mod 6: ⌊k/6⌋' if r == 0 else None))})
        items.append({'type': 'points', 'points': [at(k) for k in ks if G[k] > 0], 'color': col, 'size': 3.5})
    items.append({'type': 'points', 'points': [at(k) for k in G if G[k] == 0], 'color': L.VERDE, 'marker': 'star',
                  'size': 11, 'name': 'deg Q_k = 0: k = 3, 4, 5, 7'})
    spiral = []
    for t in range(401):
        kk = 3 + (kmax - 3) * t / 400.0
        a, r = 2 * math.pi * kk / 6.0, 0.15 + 0.85 * kk / float(kmax)
        spiral.append([1 + r * math.cos(a), 1 + r * math.sin(a), 0])
    items.append({'type': 'curve', 'points': spiral, 'color': '#D9DDE1', 'width': 1})
    for it in items:
        if it.get('name') is None:
            it.pop('name', None)
    return {'kind': '3d', 'title': 'A cone: k turns around the axis with period 6 and deg Q_k is the height. Six '
                                   'straight ladders of slope 1/6; only k ≡ 1 starts a step lower',
            'axes': ['', '', 'deg Q_k'], 'items': items}


def primes3d(cs, pmax):
    QS = [q for q in L.primes(7, pmax) if q != 5]
    a, b, c, d = cs
    disc = b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d
    pts_s, pts_n = [], []
    for q in QS:
        x = max(-1.0, min(1.0, L.a_p(q) / (2 * math.sqrt(q))))
        th = math.acos(x)
        split = (6 * a * disc) % q != 0 and len(L.roots_mod(cs, q)) == 3
        p3 = [1 + math.cos(th), 1 + math.sin(th) * 0.999, 2.4 * q / float(pmax)]
        (pts_s if split else pts_n).append((q, p3))
    cuts = sorted(set(QS[min(len(QS) - 1, int(len(QS) * f))] for f in (0.15, 0.3, 0.5, 0.7, 0.85, 1.0)))
    frames = []
    for cut in cuts:
        frames.append([{'type': 'points', 'points': [p for q, p in pts_n if q <= cut], 'color': L.AZUL, 'size': 2.6,
                        'name': 'a prime p, at the angle θ_p of a_p = 2√p cos θ_p'},
                       {'type': 'points', 'points': [p for q, p in pts_s if q <= cut], 'color': L.MORADO, 'size': 4.5,
                        'name': 'the cubic splits mod p'}])
    half = [[[1 + math.cos(math.pi * i / 24.0), 1 + math.sin(math.pi * i / 24.0), z] for z in (0, 2.4)] for i in range(25)]
    return {'kind': '3d', 'title': 'A Sato–Tate tower: each prime sits at the angle θ_p of its trace (0 to π), rising '
                                   'with p; the angles spread over the half circle as the tower grows (▶)',
            'axes': ['cos θ_p', 'sin θ_p', 'p'],
            'items': [{'type': 'surface', 'grid': half, 'color': '#C9D6E3', 'opacity': 0.18, 'name': 'the half cylinder'}],
            'slider': {'label': 'primes up to', 'values': cuts, 'items': frames, 'cumulative': False}}


def circle_frame(k):
    lo, hi = math.pi / 3, math.pi / 2

    def s_of(t):
        return (-2 * math.cos(t)) ** k + 2 * math.cos(k * t)
    ts = [lo + (hi - lo) * i / 160.0 for i in range(1, 160)]  # 25 frames: 160 points a curve keep the page light
    sv = [s_of(t) for t in ts]
    m = max(abs(x) for x in sv) or 1.0

    def P(t, s):
        c2 = 4 * math.cos(t) ** 2
        u = (1 - c2) ** 3 / c2
        lu = max(-3.0, min(3.0, math.log10(u))) if u > 0 else -3.0
        return [round(2 * (t - lo) / (hi - lo), 4), round(0.9 * s / m + 1, 4), round((lu + 3) / 3.0, 4)]
    nodes = [j * math.pi / k for j in range(int(math.ceil(k / 3.0)), k // 2 + 1)]
    pts = [lo + 1e-6] + [t for t in nodes if lo < t < hi] + [hi - 1e-6]
    roots = []
    for a, b in zip(pts, pts[1:]):
        if s_of(a) * s_of(b) < 0:
            for _ in range(70):
                mid = 0.5 * (a + b)
                if s_of(a) * s_of(mid) <= 0:
                    b = mid
                else:
                    a = mid
            roots.append(0.5 * (a + b))
    return [{'type': 'curve', 'points': [P(t, s) for t, s in zip(ts, sv)], 'color': L.AZUL, 'width': 2.6,
             'name': '(θ, s_k(θ), log u(θ))'},
            {'type': 'curve', 'points': [P(t, 0) for t in ts], 'color': L.VERDE, 'width': 1.6, 'dash': True,
             'name': 'the plane s_k = 0, along log u(θ)'},
            {'type': 'points', 'points': [P(t, 0) for t in roots], 'color': L.NARANJA, 'marker': 'star', 'size': 10,
             'name': 'the roots: one distinct u > 0 each'}]


def circle3d(k):
    ks = list(range(6, max(k, 30) + 1))
    return {'kind': '3d', 'title': 'Step one of Appendix A in space: the curve crosses the plane s_k = 0 once per '
                                   'root, each crossing at its own height log u. ▶ runs k',
            'axes': ['θ (π/3 → π/2)', 's_k (scaled)', 'log₁₀ u'], 'items': [],
            'slider': {'label': 'k', 'values': ks, 'items': [circle_frame(j) for j in ks], 'start': ks.index(k)}}
