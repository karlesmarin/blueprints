# Theorem D, n <= 6: rational dual certificates for the canonical base (anchor column fixed).
"""python zl_cert_canonica.py n [--json salida.json]"""
import itertools
import json
import sys
import time
from fractions import Fraction

import numpy as np
from ortools.linear_solver import pywraplp

n = int(sys.argv[1])
salida = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else f'cert_canonica_{n}.json'
C = tuple(range(n))
TR = [frozenset(t) for t in itertools.combinations(C, 3)]
TI = {t: i for i, t in enumerate(TR)}
NT = len(TR)
masks = np.arange(1 << NT, dtype=np.int64)
canon = masks.copy()
bits = [(masks >> i) & 1 for i in range(NT)]
for p in itertools.permutations(C[1:]):
    p = (0,) + p
    img = [TI[frozenset(p[c] for c in t)] for t in TR]
    pm = np.zeros_like(masks)
    for i in range(NT):
        pm |= bits[i] << img[i]
    np.minimum(canon, pm, out=canon)
reps = np.unique(canon)
del bits
print(f'n = {n}: {1 << NT} sombras, {len(reps)} órbitas (Sym(n-1) fijando la columna 0)', flush=True)
SOP = [frozenset(S) for k in range(2, n + 1) for S in itertools.combinations(C, k) if 0 in S]


def estructura(h):
    H = {TR[i] for i in range(NT) if h >> i & 1}
    Sl = [S for S in SOP if all(frozenset(t) in H for t in itertools.combinations(sorted(S), 3))]
    ports = [(S, j) for S in Sl for j in sorted(S) if j != 0]
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


def dual(Sl, ports, aristas):
    s = pywraplp.Solver.CreateSolver('GLOP')
    y = {p: s.NumVar(0, s.infinity(), '') for p in ports}
    lam = s.NumVar(0, s.infinity(), '')
    for a, b in aristas:
        s.Add(y[a] + y[b] >= 1)
    for S in Sl:
        s.Add(sum(y[(S, j)] for j in S if j != 0) <= lam)
    s.Minimize(lam)
    assert s.Solve() == s.OPTIMAL
    return {p: v.solution_value() for p, v in y.items()}


def exacto(Sl, aristas, yf):
    for D in (840, 2520, 27720, 720720):
        y = {p: Fraction(-int(-v * D // 1) if v > 1e-12 else 0, D) for p, v in yf.items()}
        if all(y[a] + y[b] >= 1 for a, b in aristas):
            lam = max((sum((y[(S, j)] for j in S if j != 0), Fraction(0)) for S in Sl), default=Fraction(0))
            y2 = {p: v.limit_denominator(64) for p, v in y.items()}
            if all(y2[a] + y2[b] >= 1 for a, b in aristas):
                lam2 = max((sum((y2[(S, j)] for j in S if j != 0), Fraction(0)) for S in Sl), default=Fraction(0))
                if lam2 <= lam:
                    y, lam = y2, lam2
            return lam, y
    raise RuntimeError('no se pudo redondear')


cert, mejor = [], Fraction(0)
t0 = time.time()
for k, h in enumerate(reps):
    h = int(h)
    Sl, ports, aristas = estructura(h)
    if not aristas:
        cert.append({'H_mask': h, 'dual_budget': [0, 1], 'dual_ports': [[sum(1 << c for c in S), j, 0, 1] for (S, j) in ports]})
        continue
    lam, y = exacto(Sl, aristas, dual(Sl, ports, aristas))
    mejor = max(mejor, lam)
    cert.append({'H_mask': h, 'dual_budget': [lam.numerator, lam.denominator],
                 'dual_ports': [[sum(1 << c for c in S), j, v.numerator, v.denominator] for (S, j), v in y.items()]})
    if k % 2000 == 0:
        print(f'  {k}/{len(reps)} órbitas, cota máx. {mejor} [{time.time() - t0:.0f} s]', flush=True)
json.dump({'n': n, 'orbitas': len(reps), 'cota': [mejor.numerator, mejor.denominator], 'cases': cert}, open(salida, 'w'))
print(f'RESULTADO n = {n}: pendiente canónica ≤ {mejor} ({len(reps)} órbitas) → {salida}', flush=True)
