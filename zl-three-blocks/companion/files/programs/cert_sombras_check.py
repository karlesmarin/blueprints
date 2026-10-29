# Independent checker of the shadow certificates (standard library + Fraction).
"""python cert_sombras_check.py cert_sombras_<n>.json"""
import itertools
import json
import sys
from fractions import Fraction as Q

data = json.load(open(sys.argv[1]))
n = data['n']
C = tuple(range(n))
TR = [frozenset(t) for t in itertools.combinations(C, 3)]
TI = {t: i for i, t in enumerate(TR)}
PERMS = [[TI[frozenset(p[c] for c in t)] for t in TR] for p in itertools.permutations(C)]


def orbita(h):
    idx = [i for i in range(len(TR)) if h >> i & 1]
    return {sum(1 << img[i] for i in idx) for img in PERMS}


def soporte(mask):
    return frozenset(c for c in C if mask >> c & 1)


vistos, comprob, cota = set(), 0, Q(0)
for caso in data['cases']:
    h = caso['H_mask']
    o = orbita(h)
    assert not (o & vistos), 'órbita repetida'
    vistos |= o
    H = {TR[i] for i in range(len(TR)) if h >> i & 1}
    Sl = [frozenset(S) for k in range(2, n) for S in itertools.combinations(C, k)
          if all(frozenset(t) in H for t in itertools.combinations(S, 3))]
    ports = {(S, j) for S in Sl for j in S}
    y = {}
    for mask, j, a, b in caso['dual_ports']:
        k = (soporte(mask), j)
        assert k in ports and k not in y and b > 0
        y[k] = Q(a, b)
        assert y[k] >= 0
    assert set(y) == ports, 'faltan puertos'
    lam = Q(*caso['dual_budget'])
    for S in Sl:
        for a in S:
            assert sum((y[(S, j)] for j in S if j != a), Q(0)) <= lam
            comprob += 1
    for (S, j), (T, q) in itertools.combinations(sorted(ports, key=lambda p: (sorted(p[0]), p[1])), 2):
        if S == T:
            continue
        if j == q:
            permitida = S & T == {j}
        else:
            permitida = not (q in S and j in T) and not any(frozenset((j, q, l)) in H for l in (S & T) - {j, q})
        if permitida:
            assert y[(S, j)] + y[(T, q)] >= 1, ('arista', S, j, T, q)
            comprob += 1
    cota = max(cota, lam)
assert vistos == set(range(1 << len(TR))), 'no se cubren todas las sombras'
assert Q(*data['cota']) == cota
print(f'OK n = {n}: {len(data["cases"])} órbitas disjuntas cubren las {1 << len(TR)} sombras; {comprob} desigualdades '
      f'exactas; cota α_{n} ≤ {cota}')
