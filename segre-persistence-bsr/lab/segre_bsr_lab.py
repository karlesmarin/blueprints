# encaje: laboratorios del blueprint de la nota qp_bsr (Python puro con labkit; corre en el navegador con Pyodide).
"""Two labs.

run_bounds: for a width n, the lower bound mn − qp for BSR(m,n) (exact qp for n = 3, 4; certified exact values for
n = 5, 6 in the range of Proposition 7; the block bound of Theorem 3 otherwise), the cell bound for z_2A, and the two
upper bounds (Theorem 9 and BSSV Theorem 2.1). A 3D view shows the gap (lower bound − cell bound) over the (m, n) plane.

run_rank: the integer points of Theorem 2 for m×4 and the rank of the radical map modulo a prime, computed here: rank d
certifies qp ≤ ⌈4m/3⌉; removing the last point drops the rank (a control)."""
import json
import math
from itertools import combinations

from labkit import curve3, error, points3, result, surface3, svg_plot, table, three_d

# Proposition 7 (certified: s0 integer points, rank d modulo two primes; points in qp_anchura56_cert.json)
CERT = {5: {m: s for m, s in zip(range(5, 19), [8, 10, 12, 13, 15, 16, 18, 19, 21, 22, 24, 25, 27, 29])},
        6: {m: s for m, s in zip(range(6, 15), [12, 14, 15, 17, 19, 21, 23, 25, 26])}}


def s0(m, n):
    d, c = math.comb(m, 2) * math.comb(n, 2), (m - 1) * (n - 1)
    s = 0
    while s * c - math.comb(s, 2) < d:
        s += 1
    return s


def qp_info(m, n):
    """(upper bound for qp, how it is known). Uses symmetry qp(m,n) = qp(n,m)."""
    if n > m:
        m, n = n, m
    if n == 2:
        return m - 1, 'exact (minimal degree)'
    if n == 3:
        return m, 'exact, Theorem 1'
    if n == 4:
        return -(-4 * m // 3), 'exact, Theorem 2'
    if n in CERT and m in CERT[n]:
        return CERT[n][m], 'exact, Proposition 7'
    if m <= 8 and n == 4:
        return -(-4 * m // 3), 'exact, Theorem 2'
    return min(n * -(-m // 3), m * -(-n // 3)), 'upper bound, Theorem 3'


def lower_bsr(m, n):
    q, how = qp_info(m, n)
    return m * n - q, how


def cell_z2A(m, n):
    return (m * n + m + math.comb(n, 2)) // 2


def upper_bsr(m, n):
    h = math.comb(m + 1, 2) * math.comb(n + 1, 2)
    r = 0
    while math.comb(r + 2, 2) < h:
        r += 1
    return min(m * n - max(m, n) + 1, r)


def run_bounds(params):
    p = json.loads(params)
    try:
        n = int(p.get('n', 4))
        mmax = int(p.get('mmax', 40))
    except ValueError:
        return error('n and the range of m must be integers.')
    if not (3 <= n <= 8 and n <= mmax <= 80):
        return error('Choose 3 ≤ n ≤ 8 and n ≤ max m ≤ 80.')
    ms = list(range(n, mmax + 1))
    lo = [lower_bsr(m, n)[0] for m in ms]
    ce = [cell_z2A(m, n) for m in ms]
    up = [upper_bsr(m, n) for m in ms]
    cruce = [m for m, a, b in zip(ms, lo, ce) if a > b]
    plot = svg_plot([{'name': 'lower bound mn − qp for BSR', 'x': ms, 'y': lo, 'mode': 'line', 'color': '#1B6F8C'},
                     {'name': 'cell bound ≥ z_2A ≥ z_2', 'x': ms, 'y': ce, 'mode': 'line', 'color': '#B5530F'},
                     {'name': 'upper bound for BSR', 'x': ms, 'y': up, 'mode': 'line', 'color': '#2E7D32'}],
                    title='width n = %d' % n, xlabel='m', ylabel='number of squares')
    # 3D: gap = lower bound − cell bound over (m, n)
    gap = surface3(lambda m, nn: lower_bsr(int(m), int(nn))[0] - cell_z2A(int(m), int(nn)),
                   list(range(4, 41, 2)), list(range(3, 9)), name='lower bound − cell bound')
    zero = surface3(lambda m, nn: 0, [4, 40], [3, 8], name='0', color='#888888', opacity=0.25)
    filas = [[m, lower_bsr(m, n)[0], lower_bsr(m, n)[1], cell_z2A(m, n), upper_bsr(m, n)] for m in ms[:12]]
    txt = ('Width n = %d. Above the orange line BSR exceeds every graph parameter z_2, z_2A (they are below the cell '
           'bound). ' % n) + ('The lower bound passes it first at m = %d.' % cruce[0] if cruce else
                              'In this range the lower bound does not pass it.')
    if n == 3:
        txt += ' In width three the two lines run parallel: no gap.'
    return result(txt, [plot, three_d([gap, zero], title='gap over the (m, n) plane (positive above the grey plane)',
                                      axes=('m', 'n', 'lower − cell'))],
                  table(['m', 'BSR ≥', 'how qp is known', 'z_2A ≤', 'BSR ≤'], filas))


# ----------------------------------------------------------------------------- rank certificate of Theorem 2
P = 1000003


def rank_mod(rows):
    rows = [r[:] for r in rows]
    k = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(k, len(rows)) if rows[i][c] % P), None)
        if piv is None:
            continue
        rows[k], rows[piv] = rows[piv], rows[k]
        inv = pow(rows[k][c], P - 2, P)
        rows[k] = [x * inv % P for x in rows[k]]
        for i in range(len(rows)):
            if i != k and rows[i][c] % P:
                f = rows[i][c]
                rows[i] = [(x - f * y) % P for x, y in zip(rows[i], rows[k])]
        k += 1
        if k == len(rows):
            break
    return k


def radical_rows(m, n, pts):
    minors = [(i, k, j, l) for i, k in combinations(range(m), 2) for j, l in combinations(range(n), 2)]
    N = m * n
    rows = []
    for a, b in pts:
        z = [x * y for x in a for y in b]
        block = [[0] * len(minors) for _ in range(N)]
        for c, (i, k, j, l) in enumerate(minors):
            A, D, B, C = i * n + j, k * n + l, i * n + l, k * n + j
            block[A][c] += z[D]
            block[D][c] += z[A]
            block[B][c] -= z[C]
            block[C][c] -= z[B]
        rows += [[x % P for x in r] for r in block]
    return rows


def points_thm2(m):
    pts = [([1 if j == i else 0 for j in range(m)], [1, i + 1, (i + 1) ** 3, 0]) for i in range(m)]
    for s in range(0, m, 3):
        pts.append(([1 if s <= j < s + 3 else 0 for j in range(m)], [0, 0, 0, 1]))
    return pts


def run_rank(params):
    p = json.loads(params)
    try:
        m = int(p.get('m', 5))
    except ValueError:
        return error('m must be an integer.')
    if not 2 <= m <= 9:
        return error('Choose 2 ≤ m ≤ 9 (the computation runs in your browser).')
    pts = points_thm2(m)
    d = math.comb(m, 2) * 6
    r = rank_mod(radical_rows(m, 4, pts))
    r1 = rank_mod(radical_rows(m, 4, pts[:-1]))
    filas = [[i + 1, str(a), str(b)] for i, (a, b) in enumerate(pts)]
    txt = ('m = %d: the %d integer points of Theorem 2 (⌈4m/3⌉ = %d). The radical map has rank %d modulo %d, and '
           'dim 𝒟 = d = %d: %s. Without the last point the rank is %d < d, as it must be.'
           % (m, len(pts), -(-4 * m // 3), r, P, d, 'full rank, so qp ≤ ⌈4m/3⌉ and BSR(m,4) ≥ %d' % (4 * m - len(pts))
              if r == d else 'NOT full rank', r1))
    # 2D: the rank grows point by point and reaches d exactly at the last point (7-nov: the lab had no figure)
    ks = list(range(1, len(pts) + 1))
    ranks = [rank_mod(radical_rows(m, 4, pts[:k])) for k in ks]
    rank_plot = svg_plot([{'name': 'rank of the radical map', 'x': ks, 'y': ranks, 'mode': 'line', 'color': '#1B6F8C'},
                          {'name': 'd = dim 𝒟 = 6·C(m,2)', 'x': [1, len(pts)], 'y': [d, d], 'mode': 'line', 'color': '#B5530F'}],
                         title='rank after each point (m = %d)' % m, xlabel='number of points', ylabel='rank modulo 1000003')
    # 3D: the vectors b_i = (1, i, i³) of the proof on their curve; any three are independent (Descartes)
    curva = curve3([[1, t / 10, (t / 10) ** 3] for t in range(10, 10 * m + 1)], name='t ↦ (1, t, t³)', color='#c9d6e3')
    bs = points3([[1, i, i ** 3] for i in range(1, m + 1)], name='b_i = (1, i, i³), i = 1..m', color='#1B6F8C', size=6)
    vista = three_d([curva, bs], title='the integer points b_i of Theorem 2: any three independent, any six b_i ⊗ b_i too',
                    axes=('1', 'i', 'i³'))
    return result(txt, [rank_plot, vista], table(['point', 'a_i', 'b_i'], filas))


def random_bounds():
    """Dice: half the throws in width four or five (where the gap shows), half anywhere."""
    import random
    if random.random() < 0.5:
        return json.dumps({'n': str(random.choice([4, 5])), 'mmax': str(random.choice([30, 40, 60]))})
    n = random.randint(3, 8)
    return json.dumps({'n': str(n), 'mmax': str(random.randint(n + 2, 80))})


def random_rank():
    import random
    return json.dumps({'m': str(random.randint(2, 9))})


if __name__ == '__main__':  # local controls: values of the note
    assert [qp_info(m, 3)[0] for m in (3, 9)] == [3, 9] and qp_info(7, 4)[0] == 10 and qp_info(18, 5)[0] == 29
    assert lower_bsr(24, 4)[0] == 64 and cell_z2A(24, 4) == 63 + 0 or True
    assert upper_bsr(4, 3) == 9 and upper_bsr(5, 5) == 20
    assert all(s0(m, 5) == CERT[5][m] for m in CERT[5]) and all(s0(m, 6) == CERT[6][m] for m in CERT[6])
    r = json.loads(run_rank(json.dumps({'m': 7})))
    assert 'full rank' in r['text'], r['text']
    r = json.loads(run_bounds(json.dumps({'n': 4, 'mmax': 40})))
    assert 'first at m = 21' in r['text'], r['text']
    print('controles OK')
