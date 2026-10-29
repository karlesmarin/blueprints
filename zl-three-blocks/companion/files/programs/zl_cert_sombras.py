# Proposition 6.1: rational dual certificates for every orbit of shadows (n <= 6).
"""python zl_cert_sombras.py n [--json salida.json]"""
import itertools
import json
import sys
import time
from fractions import Fraction

import numpy as np
from ortools.linear_solver import pywraplp

n = int(sys.argv[1])
salida = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else f'cert_sombras_{n}.json'
C = tuple(range(n))
TR = [frozenset(t) for t in itertools.combinations(C, 3)]
TI = {t: i for i, t in enumerate(TR)}
NT = len(TR)

# 1. órbitas bajo S_n
t0 = time.time()
masks = np.arange(1 << NT, dtype=np.int64)
canon = masks.copy()
bits = [(masks >> i) & 1 for i in range(NT)]
for p in itertools.permutations(C):
    img = [TI[frozenset(p[c] for c in t)] for t in TR]
    pm = np.zeros_like(masks)
    for i in range(NT):
        pm |= bits[i] << img[i]
    np.minimum(canon, pm, out=canon)
reps = np.unique(canon)
del bits
print(f'n = {n}: {1 << NT} sombras, {len(reps)} órbitas [{time.time() - t0:.0f} s]', flush=True)

SOP = [frozenset(S) for k in range(2, n) for S in itertools.combinations(C, k)]


def estructura(h):
    H = {TR[i] for i in range(NT) if h >> i & 1}
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


def dual(Sl, ports, aristas):
    s = pywraplp.Solver.CreateSolver('GLOP')
    y = {p: s.NumVar(0, s.infinity(), '') for p in ports}
    lam = s.NumVar(0, s.infinity(), '')
    for a, b in aristas:
        s.Add(y[a] + y[b] >= 1)
    for S in Sl:
        for a in S:
            s.Add(sum(y[(S, j)] for j in S if j != a) <= lam)
    s.Minimize(lam)
    assert s.Solve() == s.OPTIMAL
    return {p: v.solution_value() for p, v in y.items()}, lam.solution_value()


def exacto(Sl, ports, aristas, yf):
    """Redondea hacia arriba a denominador D y comprueba; devuelve (λ exacto, y racional, nº de comprobaciones)."""
    for D in (840, 2520, 27720, 720720):
        y = {p: Fraction(-int(-v * D // 1) if v > 1e-12 else 0, D) for p, v in yf.items()}
        if all(y[a] + y[b] >= 1 for a, b in aristas):
            lam = max((sum((y[(S, j)] for j in S if j != a), Fraction(0)) for S in Sl for a in S), default=Fraction(0))
            # intenta bajar a la fracción simple más cercana sin romper
            y2 = {p: v.limit_denominator(64) for p, v in y.items()}
            if all(y2[a] + y2[b] >= 1 for a, b in aristas):
                lam2 = max((sum((y2[(S, j)] for j in S if j != a), Fraction(0)) for S in Sl for a in S),
                           default=Fraction(0))
                if lam2 <= lam:
                    y, lam = y2, lam2
            return lam, y, len(aristas) + sum(len(S) for S in Sl)
    raise RuntimeError('no se pudo redondear')


cert, mejor, comprob = [], Fraction(0), 0
t0 = time.time()
for k, h in enumerate(reps):
    h = int(h)
    Sl, ports, aristas = estructura(h)
    if not ports:
        cert.append({'H_mask': h, 'dual_budget': [0, 1], 'dual_ports': []})
        continue
    yf, lf = dual(Sl, ports, aristas)
    lam, y, c = exacto(Sl, ports, aristas, yf)
    comprob += c
    mejor = max(mejor, lam)
    cert.append({'H_mask': h, 'dual_budget': [lam.numerator, lam.denominator],
                 'dual_ports': [[sum(1 << c for c in S), j, v.numerator, v.denominator] for (S, j), v in y.items()]})
    if k % 200 == 0:
        print(f'  {k}/{len(reps)} órbitas, cota máx. exacta hasta ahora {mejor} [{time.time() - t0:.0f} s]', flush=True)
json.dump({'n': n, 'orbitas': len(reps), 'cota': [mejor.numerator, mejor.denominator], 'cases': cert},
          open(salida, 'w'))
print(f'RESULTADO n = {n}: α_n ≤ {mejor} = {float(mejor):.6f} ({len(reps)} órbitas, {comprob} desigualdades exactas '
      f'comprobadas) → {salida}', flush=True)
