# Section 7: z(m, n) and the largest family by constraint programming.
"""python zl_cpsat.py — para cada (m, n): z (máximo de 1-aristas sin C4) y el máximo de 2-aristas con |E1| = z.
Controles del artículo: z_L(5,3) = 9, z_L(5,4) = 12, z_L(6,4) = 14, z_L(4,3) = 8, z_L(4,4) = 10, z_L(3,3) = 6.
Objetivo: z_L(5,5), y la comprobación explícita de que |E2| ≥ 4 es INFACTIBLE."""
import itertools
import sys

from ortools.sat.python import cp_model


def modelo(m, n, z=None, min_e2=None):
    M = cp_model.CpModel()
    celdas = [(i, j) for i in range(m) for j in range(n)]
    y = {c: M.NewBoolVar(f'y{c}') for c in celdas}
    for (r1, r2) in itertools.combinations(range(m), 2):
        for (c1, c2) in itertools.combinations(range(n), 2):
            M.AddBoolOr([y[(r1, c1)].Not(), y[(r1, c2)].Not(), y[(r2, c1)].Not(), y[(r2, c2)].Not()])
    if z is not None:
        M.Add(sum(y.values()) == z)
    pares = list(itertools.combinations(celdas, 2))
    x = {e: M.NewBoolVar(f'x{e}') for e in pares}
    for (a, b), v in x.items():
        M.AddImplication(v, y[a].Not())  # (S): las mitades no son 1-aristas
        M.AddImplication(v, y[b].Not())
    for c in celdas:  # (S): una celda es mitad de a lo sumo una 2-arista
        M.Add(sum(v for e, v in x.items() if c in e) <= 1)
    occ = {}
    for c in celdas:
        o = M.NewBoolVar(f'o{c}')
        lits = [y[c]] + [v for e, v in x.items() if c in e]
        M.AddBoolOr([o.Not()] + lits)            # o → algún literal
        for lit in lits:
            M.AddImplication(lit, o)             # literal → o
        occ[c] = o
    for ((i, j), (p, q)), v in x.items():
        nodeg = i != p and j != q
        if nodeg:  # condición 2
            M.AddBoolOr([v.Not(), occ[(i, q)].Not(), occ[(p, j)].Not()])
        for k in range(m):  # condición 3 (lectura A: también para degeneradas)
            if k in (i, p):
                continue
            for l in range(n):
                if l in (j, q):
                    continue
                cinco = {(k, l), (k, j), (k, q), (i, l), (p, l)}
                M.AddBoolOr([v.Not()] + [occ[c].Not() for c in cinco])
    if min_e2 is not None:
        M.Add(sum(x.values()) >= min_e2)
    return M, y, x


def resolver(M, maximizar=None, segundos=600):
    if maximizar is not None:
        M.Maximize(sum(maximizar))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = segundos
    s.parameters.num_workers = 4
    st = s.Solve(M)
    return s.StatusName(st), s


def z_de(m, n):
    M, y, _ = modelo(m, n)
    st, s = resolver(M, list(y.values()))
    return int(s.ObjectiveValue()) if st == 'OPTIMAL' else None


def zl_de(m, n):
    z = z_de(m, n)
    M, y, x = modelo(m, n, z=z)
    st, s = resolver(M, list(x.values()))
    return z, (z + int(s.ObjectiveValue())) if st == 'OPTIMAL' else None, st


if __name__ == '__main__':
    for m, n, esp in [(3, 3, 6), (4, 3, 8), (4, 4, 10), (5, 3, 9), (5, 4, 12), (6, 4, 14)]:
        z, v, st = zl_de(m, n)
        print(f'z_L({m},{n}) = {v}  (z = {z}, {st})  artículo {esp}  {"OK" if v == esp else "DISTINTO"}', flush=True)
    z, v, st = zl_de(5, 5)
    print(f'z_L(5,5) = {v}  (z = {z}, {st})', flush=True)
    M, y, x = modelo(5, 5, z=12, min_e2=4)
    st, _ = resolver(M)
    print(f'¿|E1| = 12 y |E2| ≥ 4 en 5×5?  {st}  (INFEASIBLE = no existe: z_L(5,5) ≤ 15)', flush=True)
    M, y, x = modelo(5, 5, z=13)
    st, _ = resolver(M)
    print(f'control: ¿13 1-aristas sin C4 en 5×5?  {st}  (debe ser INFEASIBLE: z(5,5) = 12)', flush=True)
