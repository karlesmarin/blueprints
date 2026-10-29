# encaje: CÁLCULO de los laboratorios del blueprint zl-three-blocks (Python puro, corre en Pyodide): comprobador literal de (C2)/(C3) de la Def. 2.1, base máxima, módulo de tres bloques de la Prop. 6.3 (dos regímenes, canales emparejados), M(x,y,z), λ_n, κ_n, familias de F_4 desde los datos y grafo de cajas del §8
"""Everything here follows the paper; indices from 1 in the outputs, from 0 inside."""
from fractions import Fraction
from math import comb


# ------------------------------------------------------------------ Definition 2.1, read literally
def check(E1, E2, m, n):
    """Problems of the family E2 over the base E1 in the m x n grid, as a list of (pair index, reason, detail);
    an empty list means admissible. Cells are (row, column) from 0."""
    E1 = set(E1)
    probs, seen = [], set()
    for t, (a, b) in enumerate(E2):
        for c in (a, b):
            if not (0 <= c[0] < m and 0 <= c[1] < n):
                probs.append((t, 'outside the grid', c))
            if c in E1:
                probs.append((t, 'a cell of the pair is in the base E1', c))
            if c in seen:
                probs.append((t, 'a cell is in two pairs', c))
            seen.add(c)
        if a == b:
            probs.append((t, 'the two cells are equal', a))
    O = E1 | seen
    rows, cols = {}, {}
    for (i, j) in O:
        rows.setdefault(i, set()).add(j)
        cols.setdefault(j, set()).add(i)
    for t, ((i, j), (p, q)) in enumerate(E2):
        if i != p and j != q and (i, q) in O and (p, j) in O:
            probs.append((t, '(C2): both opposite cells are occupied', ((i, q), (p, j))))
            continue
        K = (cols.get(j, set()) & cols.get(q, set())) - {i, p}
        L = (rows.get(i, set()) & rows.get(p, set())) - {j, q}
        w = next(((k, l) for k in sorted(K) for l in sorted(L) if l in rows[k]), None)
        if w:
            probs.append((t, '(C3): a witness row and column', w))
    return probs


def c4_free(E1):
    rows = {}
    for (i, j) in E1:
        rows.setdefault(i, set()).add(j)
    seen = set()
    for i, s in rows.items():
        s = sorted(s)
        for a in range(len(s)):
            for b in range(a + 1, len(s)):
                if (s[a], s[b]) in seen:
                    return False
                seen.add((s[a], s[b]))
    return True


def z_value(m, n):
    """z(m, n) in the regime m >= C(n, 2) (§1); None outside it (not needed by the labs)."""
    return m + comb(n, 2) if m >= comb(n, 2) else None


# ------------------------------------------------------------------ slopes (Theorems B, C, D; Proposition 6.3)
def lam(n):
    r = n % 3
    if r == 0:
        return Fraction(2 * n - 3, 6)
    if r == 1:
        return Fraction((n - 1) * (2 * n - 5), 6 * (n - 2))
    return Fraction((n - 2) * (2 * n - 1), 6 * (n - 1))


def kappa(n):
    return Fraction(((n - 1) ** 2) // 4, n - 1)


def M_value(x, y, z):
    """Proposition 6.3 (sizes sorted x >= y >= z >= 1): (value, regime)."""
    x, y, z = sorted((x, y, z), reverse=True)
    n = x + y + z
    if z * (x - 1) >= y * (y - 1):
        s = y + z
        return Fraction((s - 1) * ((x - 1) * s + y * z), s * (n - 2)), 1
    u = x + y - 2
    return Fraction((u + 1) * (z * u + (x - 1) * (y - 1)), u * (n - 1)), 2


def balanced(n):
    k, r = divmod(n, 3)
    return {0: (k, k, k), 1: (k + 1, k, k), 2: (k + 1, k + 1, k)}[r]


# ------------------------------------------------------------------ the module of Proposition 6.3
def three_block_module(x, y, z):
    """Rows (type, anchor column, support) and pairs of the module in the proof of Proposition 6.3 for blocks
    A, B, C of sizes x >= y >= z >= 1 (columns from 0: A first). Each pair is (cell, cell, corner) where corner is the
    block common to the two row types (the angle of the hollow triangle)."""
    x, y, z = sorted((x, y, z), reverse=True)
    A = list(range(0, x))
    B = list(range(x, x + y))
    C = list(range(x + y, x + y + z))
    blk = {'A': A, 'B': B, 'C': C}
    _, regime = M_value(x, y, z)
    if regime == 1:
        s = y + z
        plan = [('AB', 'A', z * (s - 1)), ('AC', 'A', y * (s - 1)), ('BC', 'B', (x - 1) * y), ('BC', 'C', (x - 1) * z)]
    else:
        u = x + y - 2
        plan = [('AB', 'A', z * (y - 1)), ('AB', 'B', z * (x - 1)), ('AC', 'A', (y - 1) * (u + 1)),
                ('BC', 'B', (x - 1) * (u + 1))]
    rows, turn = [], {'A': 0, 'B': 0, 'C': 0}
    for typ, anc, cnt in plan:
        for _ in range(cnt):
            col = blk[anc][turn[anc] % len(blk[anc])]
            turn[anc] += 1
            rows.append((typ, col, sorted(blk[typ[0]] + blk[typ[1]])))
    # endpoints of each row in each of its blocks
    ends = {}
    for r, (typ, anc, sup) in enumerate(rows):
        for b in typ:
            ends.setdefault((typ, b), []).extend((r, c) for c in blk[b] if c != anc)
    pairs = []
    for left, right, corner in ((('AC', 'A'), ('BC', 'B'), 'C'), (('AB', 'A'), ('BC', 'C'), 'B'),
                                (('AB', 'B'), ('AC', 'C'), 'A')):
        L, R = ends.get(left, []), ends.get(right, [])
        assert len(L) == len(R), (left, right, len(L), len(R))
        pairs += [(a, b, corner) for a, b in zip(L, R)]
    return rows, pairs, (A, B, C)


def configuration(x, y, z, copies):
    """copies of the module plus the C(n, 2) bare special rows (first): a full configuration with a maximum base."""
    n = x + y + z
    rows, pairs, blocks = three_block_module(x, y, z)
    E1, E2, corner, special = set(), [], [], comb(n, 2)
    r = 0
    for a in range(n):
        for b in range(a + 1, n):
            E1 |= {(r, a), (r, b)}
            r += 1
    for c in range(copies):
        off = special + c * len(rows)
        for k, (_, anc, _) in enumerate(rows):
            E1.add((off + k, anc))
        for (ra, ca), (rb, cb), cor in pairs:
            E2.append(((off + ra, ca), (off + rb, cb)))
            corner.append(cor)
    return special + copies * len(rows), n, E1, E2, corner, rows, blocks


# ------------------------------------------------------------------ four columns (Theorem E)
def f4_formula(m):
    if m == 6:
        return 2
    return max((2 * m - 3) // 3, (3 * m - 12) // 4)


def f4_family(data, m):
    """The witness for m >= 6 from F4_families.json (seed of the residue class + repeated module); from 0."""
    def build(rows, pairs, off=0):
        return ([{j - 1 for j in r} for r in rows], [((off + i - 1, j - 1), (off + p - 1, q - 1)) for (i, j), (p, q) in pairs])
    if m == 6:
        return build(data['m6']['rows'], data['m6']['pairs'])
    fam = data['three_quarters'] if (m >= 10 and (3 * m - 12) // 4 >= (2 * m - 3) // 3) else data['two_thirds']
    b = fam['from'] + (m - fam['from']) % fam['period']
    s = fam['seeds'][str(b)]
    T, E = build(s['rows'], s['pairs'])
    while len(T) < m:
        t, e = build(s['module_rows'], s['module_pairs'], len(T))
        T, E = T + t, E + e
    return T, E


def profile4(T, E):
    sup = [set(s) for s in T]
    for (i, j), (p, q) in E:
        sup[i].add(j)
        sup[p].add(q)
    tri = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
    return tuple(min(2, sum(1 for s in sup if set(U) <= s)) for U in tri)


# ------------------------------------------------------------------ one dimension more (§8)
def box(a, b):
    return {(u, v, w) for u in {a[0], b[0]} for v in {a[1], b[1]} for w in {a[2], b[2]}}


def box_free(S):
    S = set(S)
    L = sorted(S)
    for i, a in enumerate(L):
        for b in L[i + 1:]:
            if all(a[k] != b[k] for k in range(3)) and box(a, b) <= S:
                return False, (a, b)
    return True, None


def box_check(E1, E2):
    """§8: the two cells of every pair at distance at least 3 in the graph on O whose edges join opposite corners of
    a box with its eight cells in O. Returns [(pair index, reason)]."""
    E1 = set(E1)
    cells = {c for p in E2 for c in p}
    O = E1 | cells
    probs = []
    if len(cells) != 2 * len(E2):
        probs.append((None, 'a cell is in two pairs'))
    if cells & E1:
        probs.append((None, 'a cell of a pair is in the base'))

    def nb(a):
        return {d for d in O if all(a[k] != d[k] for k in range(3)) and box(a, d) <= O}
    for t, (a, b) in enumerate(E2):
        na = nb(a)
        if b in na:
            probs.append((t, 'distance 1: opposite corners of a full box'))
        elif na & nb(b):
            probs.append((t, 'distance 2: a common neighbour'))
    return probs


def full_rectangles(slice_cells):
    """Full 2 x 2 rectangles of a 3 x 3 slice given as a set of (i, j)."""
    out = []
    for i in range(3):
        for i2 in range(i + 1, 3):
            for j in range(3):
                for j2 in range(j + 1, 3):
                    if {(i, j), (i, j2), (i2, j), (i2, j2)} <= slice_cells:
                        out.append((i, i2, j, j2))
    return out
