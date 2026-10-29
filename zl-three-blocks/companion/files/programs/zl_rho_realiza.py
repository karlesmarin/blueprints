# Theorem C: realization of an optimal shadow program as an actual configuration (also --canonica for Theorem D).
"""python zl_rho_realiza.py n [--H 012,013,...] [--copias 2]
Sin --H: n ≤ 5 recorre todas las sombras (por fuerza bruta de órbitas) y usa la de valor máximo."""
import itertools
import sys
from fractions import Fraction
from math import comb, lcm

from ortools.linear_solver import pywraplp

from comprobar_literal_def import generalized_c4
from zl import viola

n = int(sys.argv[1])
copias = int(sys.argv[sys.argv.index('--copias') + 1]) if '--copias' in sys.argv else 2
C = tuple(range(n))
TR = [frozenset(t) for t in itertools.combinations(C, 3)]
SOP = [frozenset(S) for k in range(2, n + 1) for S in itertools.combinations(C, k)]


def estructura(H):
    Sl = [S for S in SOP if all(frozenset(t) in H for t in itertools.combinations(sorted(S), 3))]
    ports = [(S, j) for S in Sl for j in sorted(S)]
    aristas = []
    for (S, j), (T, q) in itertools.combinations(ports, 2):
        if S == T:
            continue
        if j == q:
            if S & T == {j}:
                aristas.append(((S, j), (T, q)))
            continue
        if q in S and j in T:
            continue
        if any(frozenset((j, q, l)) in H for l in (S & T) - {j, q}):
            continue
        aristas.append(((S, j), (T, q)))
    return Sl, ports, aristas


CANONICA = '--canonica' in sys.argv  # solo celdas de base en la columna 0 (base canónica de Lebedev)


def primal(Sl, ports, aristas):
    s = pywraplp.Solver.CreateSolver('GLOP')
    x = {(S, b): s.NumVar(0, 1 if (b == 0 or not CANONICA) else 0, '') for S in Sl for b in S}
    y = {e: s.NumVar(0, 1, '') for e in aristas}
    s.Add(sum(x.values()) <= 1)
    for (S, j) in ports:
        s.Add(sum(y[e] for e in aristas if (S, j) in e) <= sum(x[(S, b)] for b in S if b != j))
    s.Maximize(sum(y.values()))
    assert s.Solve() == s.OPTIMAL
    return {k: v.solution_value() for k, v in x.items()}, {k: v.solution_value() for k, v in y.items()}, s.Objective().Value()


def racional(d, den=2000):
    return {k: Fraction(v).limit_denominator(den) for k, v in d.items() if v > 1e-9}


def factible_exacto(Sl, ports, aristas, X, Y):
    if sum(X.values()) > 1:
        return False
    for (S, j) in ports:
        if sum(Y.get(e, 0) for e in aristas if (S, j) in e) > sum(X.get((S, b), 0) for b in S if b != j):
            return False
    return True


if '--H' in sys.argv:
    H = {frozenset(int(c) for c in t) for t in sys.argv[sys.argv.index('--H') + 1].split(',')}
    cand = [H]
else:
    vistos, cand = set(), []
    for mask in range(1 << len(TR)):
        H = frozenset(TR[i] for i in range(len(TR)) if mask >> i & 1)
        can = min(tuple(sorted(tuple(sorted(p[c] for c in t)) for t in H)) for p in itertools.permutations(C))
        if can not in vistos:
            vistos.add(can)
            cand.append(set(H))
mejor = None
for H in cand:
    Sl, ports, aristas = estructura(H)
    if not aristas:
        continue
    xf, yf, v = primal(Sl, ports, aristas)
    if mejor is None or v > mejor[0] + 1e-9:
        mejor = (v, H, Sl, ports, aristas, xf, yf)
v, H, Sl, ports, aristas, xf, yf = mejor
X, Y = racional(xf), racional(yf)
assert factible_exacto(Sl, ports, aristas, X, Y), 'el redondeo racional no es factible'
rho = sum(Y.values())
print(f'n = {n}: sombra óptima H = {sorted(tuple(sorted(t)) for t in H)}; LP = {v:.6f}; racional ρ = {rho}')
D = lcm(*[f.denominator for f in list(X.values()) + list(Y.values())])
Xi = {k: int(f * D) for k, f in X.items()}
Yi = {k: int(f * D) for k, f in Y.items()}
R, P = sum(Xi.values()), sum(Yi.values())
print(f'módulo: D = {D}, {R} filas etiquetadas, {P} pares (P/R = {Fraction(P, R)})')

# construcción
filas = [frozenset(p) for p in itertools.combinations(C, 2)]  # filas especiales: E1 = el par de columnas
E1, E2 = set(), []
for i, f in enumerate(filas):
    E1 |= {(i, j) for j in f}
for _ in range(copias):
    filas_lab = {}  # (S, b) -> índices de fila
    for (S, b), cnt in Xi.items():
        for _ in range(cnt):
            i = len(filas)
            filas.append(S)
            E1.add((i, b))
            filas_lab.setdefault(S, []).append((i, b))
    asign = {}
    for (S, j) in ports:
        dem = sum(Yi.get(e, 0) for e in aristas if (S, j) in e)
        libres = [i for i, b in filas_lab.get(S, []) if b != j]
        assert len(libres) >= dem
        asign[(S, j)] = [(i, j) for i in libres[:dem]]
    usado = {p: 0 for p in ports}
    for e, cnt in Yi.items():
        a, b = e
        for _ in range(cnt):
            E2.append((asign[a][usado[a]], asign[b][usado[b]]))
            usado[a] += 1
            usado[b] += 1
m = len(filas)
celdas = [c for e in E2 for c in e]
assert len(set(celdas)) == len(celdas) and not (set(celdas) & E1)
assert len(E1) == m + comb(n, 2)
lit = generalized_c4(sorted(E1), E2, m, n)
print(f'configuración {m}×{n}: |E1| = {len(E1)} = z(m,n), |E2| = {len(E2)}; literal: {lit or "ADMISIBLE"}; '
      f'viola A = {viola(E1, E2, m, n, "A")}')
