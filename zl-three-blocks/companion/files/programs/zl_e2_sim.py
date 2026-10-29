# Helper of zl_nauty.py: the family search with and without symmetry breaking.
"""python zl_e2_sim.py m n [--seg 900]   (compara con y sin ruptura en cada clase de E1 de nauty)"""
import sys
import time

from ortools.sat.python import cp_model

from zl_cpsat import modelo
from zl_cpsat_dlex import lex_ge
from zl_km import max_e2
from zl_nauty import z_mn, clases


def max_e2_sim(m, n, E1, seg):
    M, y, x = modelo(m, n, z=len(E1))
    for c, v in y.items():
        M.Add(v == (1 if c in E1 else 0))
    # ocupación por celda: 1-arista o mitad de alguna 2-arista
    occ = {}
    for i in range(m):
        for j in range(n):
            c = (i, j)
            lits = [x[e] for e in x if c in e]
            o = M.NewBoolVar(f'oc{c}')
            if c in E1:
                M.Add(o == 1)
            else:
                M.AddMaxEquality(o, lits)
            occ[c] = o
    # filas idénticas de E1: grupos; dentro de cada grupo, ocupaciones en orden lex no creciente
    grupos = {}
    for i in range(m):
        grupos.setdefault(tuple(j for j in range(n) if (i, j) in E1), []).append(i)
    for filas in grupos.values():
        for a, b in zip(filas, filas[1:]):
            lex_ge(M, [occ[(a, j)] for j in range(n)], [occ[(b, j)] for j in range(n)], f'g{a}_{b}')
    M.Maximize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = seg
    s.parameters.num_workers = 4
    st = s.StatusName(s.Solve(M))
    return st, (int(s.ObjectiveValue()) if st in ('OPTIMAL', 'FEASIBLE') else None), int(s.BestObjectiveBound())


if __name__ == '__main__':
    m, n = int(sys.argv[1]), int(sys.argv[2])
    seg = int(sys.argv[sys.argv.index('--seg') + 1]) if '--seg' in sys.argv else 900
    comparar = '--comparar' in sys.argv
    z = z_mn(m, n)
    cls = clases(m, n, z)
    mejor, exacto, t_total = -1, True, time.time()
    for k, E1 in enumerate(cls):
        t0 = time.time()
        st, e2, cota = max_e2_sim(m, n, E1, seg)
        t1 = time.time() - t0
        linea = f'  clase {k}: con ruptura {st} |E2| = {e2} (cota {cota}) [{t1:.1f} s]'
        if comparar:
            t0 = time.time()
            st2, e22, _ = max_e2(m, n, E1, seg)
            linea += f' · sin ruptura {st2} |E2| = {e22} [{time.time() - t0:.1f} s]'
        print(linea, flush=True)
        exacto = exacto and st == 'OPTIMAL'
        mejor = max(mejor, e2 if e2 is not None else -1)
    print(f'RESULTADO z_L({m},{n}) {"=" if exacto else "≥"} {z + mejor} (z = {z}, {len(cls)} clases) '
          f'[{time.time() - t_total:.0f} s]', flush=True)
