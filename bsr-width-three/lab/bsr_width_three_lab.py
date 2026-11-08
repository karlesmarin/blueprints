# encaje: laboratorio del blueprint bsr-width-three (Python puro; corre en el navegador con Pyodide y en local).
"""Two labs of «Every m×3 biquadratic sum of squares is a sum of 2m squares».

run_regular: the integer point of Lemma 2 (h = basis of ker[I P Q], Q = D P⁻¹) and the rank of dΦ_{2m} there, computed
here modulo 1000003 as the rank of the products h_a·(x_i y_j) in the space of biquadratic forms (dimension N = 3m(m+1)).
Rank N means dΦ is onto. Control: with Q = P (commuting) the rank drops.

run_witness: the form F_m = Σ_i x_i²((y₂ − i y₁)² + y₃²) of Lemma 6 with its 2m squares, checked coefficient by
coefficient; the kernels b_i = (1, i, 0) of the blocks M_i and the pairwise orthogonality of their images."""
import json
from itertools import product

import labkit as K

P = 1000003


def _key(i, k, j, l):
    return (min(i, k), max(i, k), min(j, l), max(j, l))


def _prod(u, v, m):
    """Coefficients of the biquadratic form u·v (u, v: dicts (i, j) -> int)."""
    out = {}
    for (i, j), a in u.items():
        for (k, l), b in v.items():
            kk = _key(i, k, j, l)
            out[kk] = (out.get(kk, 0) + a * b) % P
    return out


def _rank(rows):
    rows = [dict(r) for r in rows if r]
    piv = {}
    rank = 0
    for r in rows:
        r = {k: v % P for k, v in r.items() if v % P}
        while r:
            k = min(r)
            if k in piv:
                pr = piv[k]
                f = r[k] * pow(pr[k], P - 2, P) % P
                for kk, vv in pr.items():
                    r[kk] = (r.get(kk, 0) - f * vv) % P
                    if r[kk] == 0:
                        del r[kk]
            else:
                piv[k] = r
                rank += 1
                break
    return rank


def _forms_kernel(m, Q):
    """Basis of ker[I P Q] as bilinear forms: (−P e_i, e_i, 0) and (−Q e_i, 0, e_i); column j of V = coefficient of y_j."""
    Pm = [[1 if r == (c + 1) % m else 0 for c in range(m)] for r in range(m)]
    hs = []
    for M, j in ((Pm, 1), (Q, 2)):
        for i in range(m):
            h = {}
            for r in range(m):
                if M[r][i]:
                    h[(r, 0)] = (-M[r][i]) % P
            h[(i, j)] = 1
            hs.append(h)
    return hs


def _Q_default(m):
    # Q = D P^{-1}: P e_c = e_{c+1}, so P^{-1} e_c = e_{c-1}; D = diag(1..m)
    return [[(r + 1) if r == (c - 1) % m else 0 for c in range(m)] for r in range(m)]


def rank_dphi(m, Q=None):
    Q = Q if Q is not None else _Q_default(m)
    hs = _forms_kernel(m, Q)
    gens = [_prod(h, {(i, j): 1}, m) for h in hs for i in range(m) for j in range(3)]
    return _rank(gens), 3 * m * (m + 1)


def run_regular(params):
    p = json.loads(params)
    try:
        m = int(p.get('m', 4))
    except ValueError:
        return K.error('m must be an integer.')
    if not 2 <= m <= 6:
        return K.error('Choose 2 ≤ m ≤ 6 (the computation runs in your browser).')
    filas, ms, rs, ns, cs = [], [], [], [], []
    for k in range(2, m + 1):
        r, N = rank_dphi(k)
        Pm = [[1 if a == (c + 1) % k else 0 for c in range(k)] for a in range(k)]
        rc, _ = rank_dphi(k, Q=Pm)
        ms.append(k); rs.append(r); ns.append(N); cs.append(rc)
        filas.append([k, N, r, 'onto' if r == N else 'NOT onto', rc])
    plot = K.svg_plot([{'name': 'N = dim of biquadratic forms', 'x': ms, 'y': ns, 'mode': 'line', 'color': '#888888'},
                       {'name': 'rank of dΦ at [I P Q] (Lemma 2)', 'x': ms, 'y': rs, 'mode': 'points', 'color': '#1B6F8C', 'size': 7},
                       {'name': 'control: Q = P (commuting)', 'x': ms, 'y': cs, 'mode': 'points', 'color': '#B5530F', 'size': 6}],
                      title='the regular point of Lemma 2, modulo 1000003', xlabel='m', ylabel='rank')
    txt = ('For m = %d: rank of dΦ_{2m} = %d and N = %d, so dΦ is onto and the set of sums of 2m squares has interior. '
           'With Q = P the matrices commute, the argument of Lemma 2 fails and the rank is %d < N.' % (m, rs[-1], ns[-1], cs[-1]))
    return K.result(txt, [plot], K.table(['m', 'N', 'rank at [I P Q]', 'dΦ', 'rank with Q = P'], filas))


def witness_squares(m):
    """The 2m bilinear forms of F_m: x_i (y₂ − i y₁) and x_i y₃ (variables x_0.., y_0 = y₁, y_1 = y₂, y_2 = y₃)."""
    out = []
    for i in range(m):
        out.append({(i, 1): 1, (i, 0): -(i + 1)})
        out.append({(i, 2): 1})
    return out


def F_coeffs(m):
    """Coefficients of F_m = Σ x_i²((y₂ − i y₁)² + y₃²) directly from its definition."""
    out = {}
    for i in range(m):
        c = i + 1
        for kk, v in ((_key(i, i, 1, 1), 1), (_key(i, i, 0, 1), -2 * c), (_key(i, i, 0, 0), c * c), (_key(i, i, 2, 2), 1)):
            out[kk] = (out.get(kk, 0) + v) % P
    return out


def run_witness(params):
    p = json.loads(params)
    try:
        m = int(p.get('m', 4))
    except ValueError:
        return K.error('m must be an integer.')
    if not 2 <= m <= 12:
        return K.error('Choose 2 ≤ m ≤ 12.')
    sq = witness_squares(m)
    tot = {}
    for h in sq:
        for k, v in _prod(h, h, m).items():
            tot[k] = (tot.get(k, 0) + v) % P
    tot = {k: v for k, v in tot.items() if v}
    ok = tot == {k: v for k, v in F_coeffs(m).items() if v}
    # M_i: the s × 3 block of x_i; images: rows 2i, 2i+1. Inner products of the images of different blocks are zero.
    gram = [[1 if i == j else 0 for j in range(m)] for i in range(m)]
    # 3D (7-nov, Carles: «gráficos más representativos»): for each row i the set F_m(e_i, y) = 1 is the cylinder
    # (y₂ − i y₁)² + y₃² = 1 around the axis b_i = (1, i, 0): the block M_i has rank two and kernel b_i. Different axes
    # are what make M_iᵀM_j = 0, so the m planes are orthogonal and 2m squares are needed.
    import math as _m
    colores = ['#1B6F8C', '#B5530F', '#2E7D32', '#6A3D9A', '#C2185B', '#00838F']
    items = []
    filas3 = [0, 1, 2] if m >= 3 else list(range(m))   # three rows are enough to see three different axes
    for i in filas3:
        c = i + 1
        nb = _m.sqrt(1 + c * c)
        L = 4.0                                         # length along the axis, against radius 1: long tubes
        ts = [L * (k / 4 - 1.0) for k in range(9)]
        th = [2 * _m.pi * k / 16 for k in range(17)]
        items.append(K.surface3(lambda t, a, c=c, nb=nb: [t / nb, c * t / nb + _m.cos(a), _m.sin(a)], ts, th,
                                name='F(e_%d, y) = 1: tube around b_%d = (1, %d, 0)' % (c, c, c),
                                color=colores[i % len(colores)], opacity=0.15))
        items.append(K.curve3([[-1.25 * L / nb, -1.25 * L * c / nb, 0], [1.25 * L / nb, 1.25 * L * c / nb, 0]],
                              name='axis b_%d = kernel of M_%d' % (c, c), color=colores[i % len(colores)], width=6))
    vista = K.three_d(items, title='F_m(e_i, ·) = 1 is a tube around the kernel b_i of M_i: different axes in the '
                                   'plane y₃ = 0 (rows 1–%d)' % len(filas3), axes=('y₁', 'y₂', 'y₃'))
    xs = [i + 1 for i in range(m) for j in range(m)]
    ys = [j + 1 for i in range(m) for j in range(m)]
    plot = K.svg_plot([{'name': 'images of M_i and M_j orthogonal (i ≠ j): 0', 'x': [x for x, y in zip(xs, ys) if x != y],
                        'y': [y for x, y in zip(xs, ys) if x != y], 'mode': 'points', 'color': '#B5530F', 'size': 4},
                       {'name': 'same block: a plane', 'x': list(range(1, m + 1)), 'y': list(range(1, m + 1)),
                        'mode': 'points', 'color': '#1B6F8C', 'size': 7}],
                      title='m pairwise orthogonal planes force s ≥ 2m', xlabel='i', ylabel='j')
    txt = ('F_%d is the sum of the %d displayed squares: %s (coefficients compared modulo 1000003). In any representation '
           'the blocks M_i have rank two with kernel b_i, and M_iᵀM_j is antisymmetric with two independent vectors in its '
           'kernel, hence zero: the images are %d pairwise orthogonal planes, so at least %d squares are needed.'
           % (m, len(sq), 'identity checked' if ok else 'IDENTITY FAILS', m, 2 * m))
    filas = [[i + 1, 'x_%d(y₂ − %d y₁)' % (i + 1, i + 1), 'x_%d y₃' % (i + 1)] for i in range(min(m, 12))]
    return K.result(txt, [plot, vista], K.table(['i', 'square 2i − 1', 'square 2i'], filas))


def bounds(m, n):
    """(lower, upper before this note, upper after) for BSR(m, n), n = 2, 3, 4, as stated in the notes.
    n = 2: m + 1 (BPSV). n = 3: lower 2m (qp = m), upper mn − max(m,n) + 1 = 2m + 1 before, 2m after (Theorem 1).
    n = 4: lower ⌊8m/3⌋ (qp = ⌈4m/3⌉) and upper 3m + 1 (parallel-line bound), m ≥ 4."""
    if n == 2:
        return m + 1, m + 1, m + 1
    if n == 3:
        return 2 * m, 2 * m + 1, 2 * m
    return 4 * m - (-(-4 * m // 3)), 3 * m + 1, 3 * m + 1


def run_landscape(params):
    p = json.loads(params)
    try:
        mmax = int(p.get('mmax', 20))
    except ValueError:
        return K.error('the range of m must be an integer.')
    if not 4 <= mmax <= 60:
        return K.error('Choose 4 ≤ largest m ≤ 60.')
    ms = list(range(4, mmax + 1))
    # 3D (7-nov): slopes BSR/m, so the three axes have comparable scales: x = m scaled to [0, 3], y = n, z = squares/m.
    # Each width carries a ribbon between its lower and upper bound; at n = 3 the ribbon of before (2 to 2 + 1/m)
    # collapses onto the line 2 (Theorem 1); at n = 4 the ribbon from 8/3 to 3 stays open.
    xs = lambda m: 3.0 * (m - 4) / max(1, mmax - 4)
    items = []
    for n, col, op in ((2, '#888888', 0.0), (3, '#B5530F', 0.35), (4, '#2E7D32', 0.35)):
        lo = {m: bounds(m, n)[0] / m for m in ms}
        hi = {m: bounds(m, n)[1] / m for m in ms}
        if op:
            items.append(K.surface3(lambda m, s, n=n, lo=lo, hi=hi: [xs(m), n, lo[m] + s * (hi[m] - lo[m])], ms, [0.0, 1.0],
                                    name=('n = 3: the ribbon before, 2m ≤ BSR ≤ 2m + 1' if n == 3 else
                                          'n = 4: open, ⌊8m/3⌋ ≤ BSR ≤ 3m + 1'), color=col, opacity=op))
        items.append(K.curve3([[xs(m), n, lo[m]] for m in ms], name='n = %d: lower bound / m' % n,
                              color='#1B6F8C' if n == 3 else col, width=6 if n == 3 else 3))
    items.append(K.points3([[xs(m), 3, 2.0] for m in ms[::max(1, len(ms) // 12)]], name='n = 3: BSR(m,3)/m = 2 exactly (Theorem 1)',
                           color='#1B6F8C', size=5, star=True))
    vista = K.three_d(items, title='slopes BSR(m,n)/m: at n = 3 the ribbon closes to the line 2; at n = 4 it stays open',
                      axes=('m (4 → %d)' % mmax, 'n', 'squares / m'))
    # 7-nov (looked at the rendered page): the 3D view of slopes read worse than a plane figure; the idea — the n = 3
    # band closes, the n = 4 band stays open — is clearest as slopes squares/m in 2D. The 3D view is not shown.
    del vista
    sl = lambda n, k: [bounds(m, n)[k] / m for m in ms]
    plot = K.svg_plot([{'name': 'n = 4: upper bound (3m + 1)/m — open', 'x': ms, 'y': sl(4, 1), 'mode': 'line', 'color': '#2E7D32'},
                       {'name': 'n = 4: lower bound ⌊8m/3⌋/m — open', 'x': ms, 'y': sl(4, 0), 'mode': 'line', 'color': '#81C784'},
                       {'name': 'n = 3 before: upper (2m + 1)/m', 'x': ms, 'y': sl(3, 1), 'mode': 'line', 'color': '#B5530F'},
                       {'name': 'n = 3 now: BSR(m,3)/m = 2 (Theorem 1)', 'x': ms, 'y': sl(3, 2), 'mode': 'line', 'color': '#1B6F8C'},
                       {'name': 'n = 2: BSR(m,2)/m = (m + 1)/m (BPSV)', 'x': ms, 'y': sl(2, 0), 'mode': 'line', 'color': '#888888'}],
                      title='squares per row: the n = 3 band closes, the n = 4 band stays open', xlabel='m',
                      ylabel='BSR(m, n) / m', ylim=(1.0, 3.5), legend_below=True)
    plot_abs = K.svg_plot([{'name': 'n = 3, before: upper 2m + 1', 'x': ms, 'y': [bounds(m, 3)[1] for m in ms], 'mode': 'line', 'color': '#B5530F'},
                           {'name': 'n = 3: BSR(m,3) = 2m', 'x': ms, 'y': [bounds(m, 3)[2] for m in ms], 'mode': 'line', 'color': '#1B6F8C'},
                           {'name': 'n = 4: lower ⌊8m/3⌋', 'x': ms, 'y': [bounds(m, 4)[0] for m in ms], 'mode': 'line', 'color': '#81C784'},
                           {'name': 'n = 4: upper 3m + 1', 'x': ms, 'y': [bounds(m, 4)[1] for m in ms], 'mode': 'line', 'color': '#2E7D32'}],
                          title='the same, in number of squares', xlabel='m', ylabel='number of squares',
                          legend_below=True)
    filas = [[m, '%d' % bounds(m, 3)[0], '%d' % bounds(m, 3)[1], '%d' % bounds(m, 3)[2], '%d – %d' % bounds(m, 4)[:2]] for m in ms[:12]]
    txt = ('In width three the bounds were 2m ≤ BSR(m,3) ≤ 2m + 1; Theorem 1 gives 2m exactly (m = 4: 8). In width four '
           'the earlier note gives ⌊8m/3⌋ ≤ BSR(m,4) ≤ 3m + 1, still open (m = %d: %d to %d).' % (mmax, bounds(mmax, 4)[0], bounds(mmax, 4)[1]))
    return K.result(txt, [plot, plot_abs], K.table(['m', 'BSR(m,3) ≥', 'before ≤', 'now =', 'BSR(m,4) in'], filas))


def random_landscape():
    import random
    return json.dumps({'mmax': str(random.choice([10, 20, 30, 40, 60]))})


def random_regular():
    import random
    return json.dumps({'m': str(random.randint(2, 6))})


def random_witness():
    import random
    return json.dumps({'m': str(random.randint(2, 12))})


if __name__ == '__main__':  # local controls
    for m in (2, 3, 4):
        r, N = rank_dphi(m)
        assert r == N, (m, r, N)
    Pm = [[1 if a == (c + 1) % 4 else 0 for c in range(4)] for a in range(4)]
    rc, N = rank_dphi(4, Q=Pm)
    assert rc < N, rc
    r = json.loads(run_witness(json.dumps({'m': 5})))
    assert 'identity checked' in r['text'], r['text']
    r = json.loads(run_regular(json.dumps({'m': 4})))
    assert 'onto' in r['text'], r['text']
    print('controles OK; m = 4: rank', rank_dphi(4), '| control', rc)
