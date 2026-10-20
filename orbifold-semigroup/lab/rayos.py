# encaje: laboratorio del blueprint de orbifold-semigroup (Prop. 2, Figura 2); corre en el navegador con Pyodide (Lemmario).
"""Lab of Proposition 2 and Figure 2: the extreme rays of (S^1/Z_2)^k against the bound 2d - 2 of Fischer-Morris-
Shapiro (Theorem 1), BUILT from the construction of the paper, not read from 4^k and 3^k.

The construction (as in the paper's script fms_cone_gate.py): a label is a string of 2k parity bits; a fixed point is a
choice of one reflection per circle (2^k of them) and reads the k bits it chooses as a number in 0..2^k-1; the
generator of a label is the concatenation of one indicator block per fixed point. Then
  n = number of distinct generators,   d = rank of the generator matrix (exact, modulo a large prime),
and every generator is an extreme ray (a 0/1 vector with one 1 per block is a vertex of the product of simplices; the
proof of Proposition 2). For k above the computed range the lab says so and shows only 4^k and 3^k from the formula.
"""
import json
from itertools import product

P = 2 ** 61 - 1  # rank over Q equals rank mod P here (0/1 matrix; checked against exact rationals for k <= 2)


def generators(k):
    gens = set()
    for t in product((0, 1), repeat=2 * k):
        v = []
        for choice in product((0, 1), repeat=k):
            val = 0
            for c in range(k):
                val = 2 * val + t[2 * c + choice[c]]
            blk = [0] * (2 ** k)
            blk[val] = 1
            v.extend(blk)
        gens.add(tuple(v))
    return sorted(gens)


def rank_mod(rows, p=P):
    rows = [list(r) for r in rows]
    rk, col, m = 0, 0, len(rows[0]) if rows else 0
    for col in range(m):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [x * inv % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def rank_exact(rows):
    from fractions import Fraction
    rows = [[Fraction(x) for x in r] for r in rows]
    rk = 0
    for col in range(len(rows[0])):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][col] != 0:
                f = rows[i][col] / rows[rk][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def run(arg):
    a = json.loads(arg or '{}')
    K = max(1, min(int(a.get('kmax', 6)), 10))
    computed = min(K, 4)
    rows, ks, ns, bounds, ratios = [], [], [], [], []
    for k in range(1, K + 1):
        if k <= computed:
            g = generators(k)
            n, d = len(g), rank_mod(g)
            if k <= 2 and rank_exact(g) != d:
                return json.dumps({'error': 'the rank modulo P differs from the exact rank at k = %d' % k})
            how = 'built and counted'
            ok = (n == 4 ** k and d == 3 ** k)
        else:
            n, d, how, ok = 4 ** k, 3 ** k, 'formula only (4^k, 3^k): not rebuilt here', True
        b = 2 * d - 2
        verdict = 'bound met exactly' if n == b else ('over the bound: not a complete intersection' if n > b else 'under the bound')
        rows.append([k, n, d, b, '%.4f' % (n / b if b else float('inf')), verdict, how + ('' if ok else '  ⚠ differs from 4^k, 3^k')])
        ks.append(k); ns.append(n); bounds.append(b); ratios.append(n / b if b else None)
    text = ('Every generator is a 0/1 vector with one 1 in each of the 2^k fixed-point blocks, hence a vertex of the '
            'product of simplices and an extreme ray. Theorem 1 needs n ≤ 2d − 2 for a complete intersection. '
            'Built up to k = %d (n and the exact rank d of the generator matrix); the ratio is exactly 1 at k = 1, 2 '
            'and exceeds 1 from k = 3, as in Figure 2.' % computed)
    return json.dumps({
        'text': text,
        'table': {'head': ['k', 'n (extreme rays)', 'd = dim S', '2d − 2', 'n / (2d − 2)', 'verdict', 'how'], 'rows': rows},
        'plots': [
            {'title': 'extreme rays n and the bound 2d − 2 (Theorem 1)', 'xlabel': 'k', 'ylabel': 'count', 'x': ks,
             'series': [{'name': 'n = extreme rays', 'y': ns}, {'name': '2d − 2', 'y': bounds}]},
            {'title': 'the ratio n / (2d − 2): 1 means the bound is met, above 1 it is violated', 'xlabel': 'k',
             'ylabel': 'ratio', 'x': ks, 'series': [{'name': 'n / (2d − 2)', 'y': ratios}, {'name': '1', 'y': [1] * len(ks)}]},
        ]})


if __name__ == '__main__':
    print(run(json.dumps({'kmax': 6})))
