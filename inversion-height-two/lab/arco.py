# encaje: laboratorio del blueprint de inversion-height-two (Lemas 4.1–4.2); corre en el navegador con Pyodide (Lemmario).
"""Lab of Lemmas 4.1 and 4.2: the exact arc γ_k and Smith profiles, in exact integer arithmetic.

U_0 = -(t E12 + ε E21), K = I + t E21, U_i = K^i U_0 K^-i (i = 0, 1, 2 for u, v, w), and γ_k takes ε = t^k.
Lemma 4.1: tr U_i = 0, det U_i = -tε, U_i^2 = tε I, so U_i(t, t^k)^2 = t^(k+1) I and U_i has Smith parts (1, k).
Lemma 4.2(1): a matrix with entries in the squares (here the target H_0 = [[u²+v², u²], [u², u²+w²]]) evaluates to a
multiple of t^(k+1), so all its 2d parts reach level k+1; Lemma 4.4: an allowed denominator has at most 2 parts there.
A polynomial in t is a list of integer coefficients (index = degree)."""
from fractions import Fraction
import itertools
import json
import math


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pneg(a):
    return [-x for x in a]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1) if a and b else [0]
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out


def val(a):
    """t-adic valuation (None for the zero polynomial)."""
    return next((i for i, x in enumerate(a) if x), None)


def mmul(A, B):
    n, m, r = len(A), len(B), len(B[0])
    return [[sum_poly([pmul(A[i][k], B[k][j]) for k in range(m)]) for j in range(r)] for i in range(n)]


def sum_poly(ps):
    s = [0]
    for p in ps:
        s = padd(s, p)
    return s


def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    s = [0]
    for j in range(n):
        minor = [row[:j] + row[j + 1:] for row in M[1:]]
        term = pmul(M[0][j], det(minor))
        s = padd(s, term if j % 2 == 0 else pneg(term))
    return s


def smith_parts(M):
    """Exponents of the invariant factors over Q[[t]]: d_j = least valuation of the j×j minors, parts d_j - d_{j-1}
    (an infinite part, ∞, when every j×j minor vanishes)."""
    n = len(M)
    parts, prev = [], 0
    for j in range(1, n + 1):
        vs = [val(det([[M[r][c] for c in cs] for r in rs])) for rs in itertools.combinations(range(n), j)
              for cs in itertools.combinations(range(n), j)]
        vs = [v for v in vs if v is not None]
        if not vs:
            parts += [None] * (n - j + 1)
            break
        d = min(vs)
        parts.append(d - prev)
        prev = d
    return parts


def nu(parts, j):
    return sum(1 for p in parts if p is None or p >= j)


def U(i, k):
    t, eps = [0, 1], [0] * k + [1]
    U0 = [[[0], pneg(t)], [pneg(eps), [0]]]
    Ki = [[[1], [0]], [[0, i], [1]]]       # K^i = I + i t E21
    Kmi = [[[1], [0]], [[0, -i], [1]]]     # K^-i = I - i t E21
    return mmul(mmul(Ki, U0), Kmi)


def show(p):
    """The polynomial as text, highest degree last, with one kind of minus sign."""
    out = ''
    for d, c in enumerate(p):
        if not c:
            continue
        mag = abs(c)
        body = '%d' % mag if d == 0 else ('' if mag == 1 else '%d' % mag) + ('t' if d == 1 else 't^%d' % d)
        if not out:
            out = ('−' if c < 0 else '') + body
        else:
            out += (' − ' if c < 0 else ' + ') + body
    return out or '0'


def run(params):
    p = json.loads(params)
    try:
        k = int(p.get('k', 3))
    except ValueError:
        return json.dumps({'error': 'k must be an integer'})
    if not 1 <= k <= 12:
        return json.dumps({'error': 'k must be between 1 and 12'})
    rows, sq = [], []
    for i, name in enumerate('uvw'):
        Ui = U(i, k)
        tr = padd(Ui[0][0], Ui[1][1])
        d = det(Ui)
        S = mmul(Ui, Ui)
        scalar = S[0][1] == [0] * len(S[0][1]) and val(S[1][0]) is None and S[0][0] == S[1][1]
        sq.append(S)
        rows.append(['%s → U_%d' % (name, i), '[[%s, %s], [%s, %s]]' % tuple(show(x) for x in (Ui[0][0], Ui[0][1], Ui[1][0], Ui[1][1])),
                     show(tr), show(d), ('%s · I' % show(S[0][0])) if scalar else 'NOT scalar', str(tuple(smith_parts(Ui)))])
    # target H_0 = [[u²+v², u²], [u², u²+w²]] on γ_k, as a 4×4 matrix
    u2, v2, w2 = sq
    blocks = [[[[padd(u2[r][s], v2[r][s]) for s in range(2)] for r in range(2)], u2],
              [u2, [[padd(u2[r][s], w2[r][s]) for s in range(2)] for r in range(2)]]]
    H = [[blocks[R][C][r][s] for C in range(2) for s in range(2)] for R in range(2) for r in range(2)]
    hp = smith_parts(H)
    rows.append(['H₀ = [[u²+v², u²], [u², u²+w²]]', '4×4 on γ_%d' % k, '', show(det(H)), '', str(tuple(hp))])
    js = list(range(1, k + 3))
    up = smith_parts(U(0, k))
    plot = {'title': 'Smith profile ν_j on γ_%d: target H₀ against an allowed denominator' % k, 'xlabel': 'level j',
            'ylabel': 'ν_j = number of parts ≥ j', 'x': js, 'step': True,
            'series': [{'name': 'target H₀ (Lemma 4.2): 4 parts at level k+1', 'y': [nu(hp, j) for j in js]},
                       {'name': 'a letter U_i: parts (1, k)', 'y': [nu(up, j) for j in js]},
                       {'name': 'bound on allowed denominators at level k+1 (Lemma 4.4)', 'dash': True,
                        'y': [2 if j == k + 1 else None for j in js]}]}
    fig_a, worst = figure_2a(k)
    text = ('On γ<sub>%d</sub> every square is the same scalar t<sup>%d</sup>I (Lemma 4.1), so the target H₀ has all four '
            'parts at level %d: ν<sub>%d</sub>(H₀) = %d, against at most 2 for every allowed denominator (Lemma 4.4) — the '
            'margin 4 − 2 of Theorem 5.1. Figure 2 of the paper is redrawn for this k in its place: (a) in 3D, drag it to turn '
            'it, press ▶ to move t; at every t of the slider the three points lie exactly on the quadric '
            'a² + p² − q² = t<sup>%d</sup> (checked in exact fractions: largest gap %s); (b) the scalar of the squares.'
            % (k, k + 1, k + 1, k + 1, nu(hp, k + 1), k + 1, worst))
    return json.dumps({'text': text, 'table': {'head': ['letter', 'U_i(t, t^k)', 'trace', 'determinant', 'U_i²',
                                                         'Smith parts'], 'rows': rows},
                       'plots': [plot, fig_a, figure_2b(sq, k)]})


def peval(p, t):
    return sum(c * t ** d for d, c in enumerate(p))


LETTERS = [('u', '#0072B2'), ('v', '#56B4E9'), ('w', '#222222')]  # the paper's colours (figuras/estilo.py)


def apq(M, t):
    """The point (a, p, q) of a traceless 2×2 matrix of polynomials at t: a = U11, p = (U12 + U21)/2,
    q = (U12 − U21)/2, so that U² = (a² + p² − q²) I (the coordinates of Figure 2)."""
    a, b, c = (peval(M[0][0], t), peval(M[0][1], t), peval(M[1][0], t))
    return a, (b + c) / 2, (b - c) / 2


def sheet(level, n_r=10, n_phi=28, r_max=2.2):
    """The sheet q ≤ 0 of a² + p² − q² = level, as a grid: (ρ cos φ, ρ sin φ, −r) with ρ = √(level + r²); level 0 is
    the cone of nilpotent matrices, where the parabolic family ε = 0 lies."""
    rs = [r_max * i / n_r for i in range(n_r + 1)]
    phis = [2 * math.pi * j / n_phi for j in range(n_phi + 1)]
    return [[[round(math.sqrt(level + r * r) * math.cos(f), 4), round(math.sqrt(level + r * r) * math.sin(f), 4),
              round(-r, 4)] for f in phis] for r in rs]


def figure_2a(k):
    """Figure 2(a) of the paper in 3D for the reader's k, with t on a slider: the curves of u, v, w on γ_k (solid) and
    for ε = 0 (dashed, on the cone), and at each t the three points U_i(t, t^k) with the quadric a² + p² − q² = t^(k+1)
    they lie on. Returns the figure and the largest exact gap |a² + p² − q² − t^(k+1)| over the points shown."""
    curve = [i / 40 for i in range(41)]
    items = [{'type': 'surface', 'grid': sheet(0), 'color': '#999999', 'opacity': 0.06,
              'name': 'cone a² + p² = q² (U² = 0)'}]
    for i, (name, col) in enumerate(LETTERS):
        Ui, Ui0 = U(i, k), U0_parabolic(i)
        items.append({'type': 'curve', 'color': col, 'width': 3,
                      'points': [[round(x, 4) for x in apq(Ui, t)] for t in curve],
                      'name': '%s → U_%d(t, t^%d), t ∈ [0, 1]' % (name, i, k)})
        items.append({'type': 'curve', 'color': col, 'width': 1.6, 'dash': True,
                      'points': [[round(x, 4) for x in apq(Ui0, t)] for t in curve],
                      'name': '%s at ε = 0 (parabolic family)' % name})
    values, frames, worst = [Fraction(n, 20) for n in range(21)], [], Fraction(0)
    for t in values:
        pts = []
        for i, (name, col) in enumerate(LETTERS):
            a, p, q = apq(U(i, k), t)  # exact: t is a fraction
            worst = max(worst, abs(a * a + p * p - q * q - t ** (k + 1)))
            pts.append({'type': 'points', 'marker': 'star', 'color': col, 'points': [[float(a), float(p), float(q)]],
                        'name': '%s at t = %s' % (name, float(t))})
        lev = float(t ** (k + 1))
        frames.append([{'type': 'surface', 'grid': sheet(lev), 'color': '#CC79A7', 'opacity': 0.22,
                        'name': 'quadric a² + p² − q² = t^%d = %.4g' % (k + 1, lev)}] + pts)
    fig = {'kind': '3d', 'title': 'Figure 2(a) for k = %d: the arc γ_%d leaves the cone, at each t on one quadric' % (k, k),
           'axes': ['a', 'p', 'q'], 'items': items,
           'slider': {'label': 't', 'values': [float(t) for t in values], 'items': frames, 'start': len(values) - 1},
           'figure': 'fig_3_arco_exacto', 'panel': 'a'}  # drawn in place of the paper's Figure 2 (lab.js)
    return fig, str(worst)


def U0_parabolic(i):
    """U_i(t, 0) = K^i U_0 K^-i with ε = 0 (U² = 0: the parabolic family, on the cone)."""
    t = [0, 1]
    U0 = [[[0], pneg(t)], [[0], [0]]]
    return mmul(mmul([[[1], [0]], [[0, i], [1]]], U0), [[[1], [0]], [[0, -i], [1]]])


def figure_2b(sq, k):
    """Figure 2(b) for the reader's k: the scalar λ with U_i(t, t^k)² = λI, read off the exact squares of u, v, w
    (their (1,1) entry; the table above checks that each square is scalar), against t^(k+1): the curves coincide."""
    ts = [round(0.05 * n, 2) for n in range(25)]  # t = 0, 0.05, …, 1.2, as in the paper's figure
    series = [{'name': '%s → U_%d(t, t^%d)²' % (name, i, k), 'y': [round(peval(sq[i][0][0], t), 6) for t in ts]}
              for i, name in enumerate('uvw')]
    series.append({'name': 't^%d (Lemma 4.1)' % (k + 1), 'dash': True, 'y': [round(t ** (k + 1), 6) for t in ts]})
    return {'title': 'Figure 2(b) for k = %d: the scalar λ with U_i(t, t^%d)² = λI — the three curves coincide' % (k, k),
            'xlabel': 't', 'ylabel': 'λ', 'x': ts, 'step': False, 'series': series,
            'figure': 'fig_3_arco_exacto', 'panel': 'b'}
