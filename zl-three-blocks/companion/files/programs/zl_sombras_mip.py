# Theorem B, n = 7: the shadow as 0/1 variables in one mixed integer program (floating point, evidence only).
"""python zl_sombras_mip.py [--nmax 7] [--seg 3600]"""
import itertools
import sys
from fractions import Fraction

from ortools.linear_solver import pywraplp


def formula(n):
    r = n % 3
    if r == 0:
        return Fraction(n * (2 * n - 3), 6 * n)
    if r == 1:
        return Fraction((n - 1) * (2 * n - 5), 6 * (n - 2))
    return Fraction((n - 2) * (2 * n - 1), 6 * (n - 1))


def mip(n, seg, solver='SCIP'):
    s = pywraplp.Solver.CreateSolver(solver)
    s.SetTimeLimit(seg * 1000)
    if solver == 'HIGHS':
        s.SetNumThreads(4)
    C = range(n)
    triples = [frozenset(t) for t in itertools.combinations(C, 3)]
    h = {t: s.BoolVar('') for t in triples}
    sops = [frozenset(S) for k in range(2, n) for S in itertools.combinations(C, k)]
    sv = {S: s.BoolVar('') for S in sops}
    for S in sops:
        for t in itertools.combinations(sorted(S), 3):
            s.Add(sv[S] <= h[frozenset(t)])
    x = {(S, a): s.NumVar(0, 1, '') for S in sops for a in S}
    for (S, a), v in x.items():
        s.Add(v <= sv[S])
    s.Add(sum(x.values()) <= 1)
    ports = [(S, j) for S in sops for j in S]
    inc = {p: [] for p in ports}
    f = []
    for (S, j), (T, q) in itertools.combinations(ports, 2):
        if S == T:
            continue
        if j == q:
            if S & T != {j}:
                continue
            bloq = []
        else:
            if q in S and j in T:
                continue
            bloq = [frozenset((j, q, l)) for l in (S & T) - {j, q}]
        v = s.NumVar(0, 1, '')
        for t in bloq:
            s.Add(v <= 1 - h[t])
        inc[(S, j)].append(v)
        inc[(T, q)].append(v)
        f.append(v)
    for (S, j) in ports:
        if inc[(S, j)]:
            s.Add(sum(inc[(S, j)]) <= sum(x[(S, a)] for a in S if a != j))
    s.Maximize(sum(f))
    st = s.Solve()
    nombre = {s.OPTIMAL: 'OPTIMAL', s.FEASIBLE: 'FEASIBLE'}.get(st, str(st))
    H = sorted(tuple(sorted(t)) for t in triples if h[t].solution_value() > 0.5) if st in (s.OPTIMAL, s.FEASIBLE) else None
    filas = {(tuple(sorted(S)), a): round(v.solution_value(), 4) for (S, a), v in x.items()
             if v.solution_value() > 1e-6} if H is not None else None
    return nombre, s.Objective().Value(), s.Objective().BestBound(), len(f), H, filas


if __name__ == '__main__':
    nmax = int(sys.argv[sys.argv.index('--nmax') + 1]) if '--nmax' in sys.argv else 7
    seg = int(sys.argv[sys.argv.index('--seg') + 1]) if '--seg' in sys.argv else 3600
    for n in range(3, nmax + 1):
        st, val, cota, ne, H, filas = mip(n, seg)
        fo = formula(n)
        print(f'n = {n}: MIP {st} valor {val:.6f} cota {cota:.6f} ({ne} aristas); fórmula plantillas {fo} = '
              f'{float(fo):.6f} → {"COINCIDE" if abs(cota - float(fo)) < 1e-6 else "DIFIERE"}', flush=True)
        print(f'    H = {H}', flush=True)
        print(f'    filas = {filas}', flush=True)
