# encaje: laboratorio del blueprint bsr-four-four (Lema 4, punto regular): rango de los productos de los sumandos simétricos
"""Lab of Lemma 4 of «Every 4×4 biquadratic sum of squares is a sum of eleven squares».

The summands are the n forms x_i y_i and the C(n,2) forms x_i y_j + x_j y_i. Their products with all monomials
x_a y_b span the biquadratic forms (dimension C(n+1,2)²) exactly when no non-zero multiplier vanishes on their span:
d Φ is then onto. The rank is computed modulo the prime 1000003, adding the summands one at a time in the order
chosen by the seed. Pure Python: it runs in the browser (Pyodide)."""
import json
import random

import labkit as K

P = 1000003


def summands(n):
    """[(name, {(i, j): c})]: the diagonal ones first, then the symmetric pairs."""
    out = [('x%dy%d' % (i + 1, i + 1), {(i, i): 1}) for i in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            out.append(('x%dy%d+x%dy%d' % (i + 1, j + 1, j + 1, i + 1), {(i, j): 1, (j, i): 1}))
    return out


def _key(i, k, j, l):
    return (min(i, k), max(i, k), min(j, l), max(j, l))


def products(h, n):
    """The products of the bilinear form h with every monomial x_a y_b, as dicts on biquadratic monomials."""
    rows = []
    for a in range(n):
        for b in range(n):
            r = {}
            for (i, j), c in h.items():
                k = _key(i, a, j, b)
                r[k] = (r.get(k, 0) + c) % P
            rows.append({k: v for k, v in r.items() if v})
    return rows


class Echelon:
    """Incremental row echelon form modulo P; add() returns True when the row is independent."""

    def __init__(self):
        self.piv = {}

    def add(self, row):
        row = dict(row)
        while row:
            k = min(row)
            if k not in self.piv:
                inv = pow(row[k], P - 2, P)
                self.piv[k] = {kk: v * inv % P for kk, v in row.items()}
                return True
            f = row[k]
            for kk, v in self.piv[k].items():
                row[kk] = (row.get(kk, 0) - f * v) % P
            row = {kk: v for kk, v in row.items() if v}
        return False

    def rank(self):
        return len(self.piv)


def ranks(n, seed=0, drop=None):
    """Ranks after each summand (order shuffled by seed; seed 0 keeps the paper's order); drop: index left out."""
    S = summands(n)
    order = list(range(len(S)))
    if seed:
        random.Random(seed).shuffle(order)
    if drop is not None:
        order = [i for i in order if i != drop]
    E = Echelon()
    out = []
    for i in order:
        for r in products(S[i][1], n):
            E.add(r)
        out.append((S[i][0], E.rank()))
    return out


def run_regular(params):
    p = json.loads(params)
    try:
        n = int(p.get('n', 4))
        seed = int(p.get('seed', 0))
    except ValueError:
        return K.error('n and the seed must be integers.')
    if not 2 <= n <= 5:
        return K.error('Choose 2 ≤ n ≤ 5 (the computation runs in your browser).')
    N = (n * (n + 1) // 2) ** 2
    full = ranks(n, seed)
    diag = ranks(n, 0)[:n]
    short = ranks(n, 0, drop=len(summands(n)) - 1)
    xs = list(range(1, len(full) + 1))
    fig = K.svg_plot([
        {'name': 'rank after k summands (this order)', 'x': xs, 'y': [r for _, r in full], 'mode': 'line'},
        {'name': 'dimension of the biquadratic forms, %d' % N, 'x': [1, len(full)], 'y': [N, N], 'mode': 'line',
         'color': '#999999'},
    ], title='n = %d: the products of the summands with V fill R₂' % n, xlabel='summands used',
        ylabel='rank modulo 1000003', legend_below=True)
    rows = [[k + 1, name, r, 'onto' if r == N else ''] for k, (name, r) in enumerate(full)]
    txt = ('For n = %d the %d symmetric summands give rank %d out of N = %d, so dΦ is onto at that point (with one more '
           'zero summand when n = 4, the point of Lemma 4). Controls: the %d diagonal summands alone give %d; leaving '
           'out the last pair gives %d < N. A multiplier vanishing on the span of all of them vanishes on every '
           'symmetric tensor, and the Hankel symmetry then forces it to be zero (the argument of Lemma 4, checked in '
           'Isabelle as regular_point_symmetric).'
           % (n, len(full), full[-1][1], N, n, diag[-1][1], short[-1][1]))
    return K.result(txt, [fig], K.table(['k', 'summand added', 'rank', ''], rows))


def random_regular():
    return json.dumps({'n': str(random.randint(2, 5)), 'seed': str(random.randint(1, 999))})


if __name__ == '__main__':
    for n in (2, 3, 4, 5):
        f = ranks(n)
        print(n, (n * (n + 1) // 2) ** 2, f[-1][1], ranks(n)[:n][-1][1], ranks(n, 0, drop=len(summands(n)) - 1)[-1][1])
