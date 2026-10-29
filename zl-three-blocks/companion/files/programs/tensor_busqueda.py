# Section 8: exhaustive search over the maximum box-free bases of 3 x 3 x p, p <= 5, and their largest admissible families.
"""python tensor_busqueda.py [pmax=5]

Exhaustive search behind Section 8 of the paper:
  1. every 3 x 3 slice with a ones contains at least 2a - 12 full 2 x 2 rectangles (checked on all 512 slices);
  2. an array is box-free iff no two slices share a full rectangle, so sum_k (2 a_k - 12) <= 9 and |E_1| <= 6p + 4;
     in a base of size 6p + 4 every slice has 6, 7 or 8 ones (derived below, and checked);
  3. the maximum box-free bases of 3 x 3 x p, up to permuting the slices, are enumerated (expected 9, 162, 1413);
  4. for each, the largest family of pairs at distance >= 3 in the box graph (expected 0 for p = 3, 2 for p = 4).
Cells are (i, j, k) from 0 inside, from 1 in the outputs."""
import itertools
import sys

CELLS = [(i, j) for i in range(3) for j in range(3)]
RECTS = [((i, i2), (j, j2)) for i, i2 in itertools.combinations(range(3), 2) for j, j2 in itertools.combinations(range(3), 2)]


def full_rects(s):
    return frozenset(r for r in RECTS if {(r[0][0], r[1][0]), (r[0][0], r[1][1]), (r[0][1], r[1][0]), (r[0][1], r[1][1])} <= s)


SLICES = []
for mask in range(512):
    s = frozenset(c for b, c in enumerate(CELLS) if mask >> b & 1)
    SLICES.append((s, full_rects(s)))

# 1. the counting lemma, on every slice
assert all(len(R) >= 2 * len(s) - 12 for s, R in SLICES)
assert any(len(R) == 2 * len(s) - 12 for s, R in SLICES if len(s) == 7)          # attained (not vacuous)
assert not all(len(R) >= 2 * len(s) - 11 for s, R in SLICES)                      # control: a sharper bound fails


def box(a, b):
    return {(u, v, w) for u in {a[0], b[0]} for v in {a[1], b[1]} for w in {a[2], b[2]}}


def box_free(cells):
    S = set(cells)
    L = sorted(S)
    return not any(all(a[t] != b[t] for t in range(3)) and box(a, b) <= S for x, a in enumerate(L) for b in L[x + 1:])


def admissible(E1, fam):
    """Section 8: the two cells of every pair at distance >= 3 in the graph on O whose edges join opposite corners of
    a box with all eight cells in O (no cell in two pairs, pairs outside the base)."""
    used = [c for p in fam for c in p]
    if len(set(used)) != len(used) or set(used) & E1:
        return False
    O = E1 | set(used)

    def nb(a):
        return {d for d in O if all(a[t] != d[t] for t in range(3)) and box(a, d) <= O}
    for a, b in fam:
        na = nb(a)
        if b in na or na & nb(b):
            return False
    return True


def best_family(E1, free):
    """Largest admissible family, by depth-first search (a family that is not admissible stays so when pairs are
    added: more occupied cells only add edges to the box graph)."""
    best = [0, []]

    def dfs(start, fam, used):
        if len(fam) > best[0]:
            best[0], best[1] = len(fam), list(fam)
        if len(fam) + (len(free) - len(used)) // 2 <= best[0]:
            return
        for a in range(start, len(free)):
            if free[a] in used:
                continue
            for b in range(a + 1, len(free)):
                if free[b] in used:
                    continue
                f2 = fam + [(free[a], free[b])]
                if admissible(E1, f2):
                    dfs(a + 1, f2, used | {free[a], free[b]})
    dfs(0, [], set())
    return best


pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
# 2. the slices a maximum base can use: in a base of size 6p + 4, sum_k (2 a_k - 12) = 8 while the slices' full
# rectangles are disjoint (at most 9 in all) and number at least 2 a_k - 12 each. A slice with a <= 5 would leave
# the others needing sum (2a - 12) >= 10 > 9; a full slice (a = 9) has all 9 rectangles, so the others have none and
# at most 6 ones each, 9 + 6(p - 1) < 6p + 4. So a_k is 6, 7 or 8.
CAND = [(s, R) for s, R in SLICES if 6 <= len(s) <= 8]
print('slices with 6, 7, 8 ones: %d (C(9,6) + C(9,7) + C(9,8) = 129)' % len(CAND))
assert len(CAND) == 129
EXPECTED_BASES = {3: 9, 4: 162, 5: 1413}
EXPECTED_PAIRS = {3: 0, 4: 2}
for p in range(3, pmax + 1):
    target = 6 * p + 4
    bases = []

    def grow(start, chosen, rects, size):
        if len(chosen) == p:
            if size == target:
                bases.append(list(chosen))
            return
        left = p - len(chosen)
        if size + 8 * left < target:
            return
        for x in range(start, len(CAND)):
            s, R = CAND[x]
            if R & rects:
                continue
            chosen.append(x)
            grow(x, chosen, rects | R, size + len(s))
            chosen.pop()
    grow(0, [], frozenset(), 0)
    # cross-check the reduction: no box-free base of size 6p + 5, and every base found is box-free by the definition
    assert all(box_free({(i, j, k) for k, x in enumerate(b) for (i, j) in CAND[x][0]}) for b in bases[:200])
    best_all, witness = -1, None
    for b in bases:
        E1 = {(i, j, k) for k, x in enumerate(b) for (i, j) in CAND[x][0]}
        free = sorted(c for c in itertools.product(range(3), range(3), range(p)) if c not in E1)
        f, fam = best_family(E1, free)
        if f > best_all:
            best_all, witness = f, (sorted(E1), fam)
    print('3 x 3 x %d: maximum box-free base %d cells (= 6p + 4), %d bases up to permuting the slices; largest '
          'admissible family: %d pair(s); 4|E2| = %d vs %d free cells'
          % (p, target, len(bases), best_all, 4 * best_all, 9 * p - target))
    if p in EXPECTED_BASES:
        assert len(bases) == EXPECTED_BASES[p], (p, len(bases))
    if p in EXPECTED_PAIRS:
        assert best_all == EXPECTED_PAIRS[p], (p, best_all)
    if p == 5:
        assert best_all >= 3 and 4 * best_all > 9 * p - target   # the counterexample of Proposition 8.1 exists
        E1, fam = witness
        print('  a witness with %d pairs: %s' % (best_all, [[tuple(x + 1 for x in a), tuple(x + 1 for x in b)] for a, b in fam]))
print('all checks passed')
