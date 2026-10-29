# Section 7: the same with double-lex symmetry breaking (second, independent run).
"""python zl_cpsat_dlex.py m n [--simetria-cpsat] [--seg 1800]"""
import sys
import time

from ortools.sat.python import cp_model

from zl_cpsat import modelo, z_de


def lex_ge(M, a, b, nombre):
    """Restricción a ≥_lex b para listas de Bool (desde la primera posición): con variables «iguales hasta i»."""
    k = len(a)
    eq = [M.NewBoolVar(f'{nombre}_eq{i}') for i in range(k + 1)]
    M.Add(eq[0] == 1)
    for i in range(k):
        # mientras sean iguales hasta i: a_i ≥ b_i; eq_{i+1} = eq_i ∧ (a_i == b_i)
        M.Add(a[i] >= b[i]).OnlyEnforceIf(eq[i])
        iguales = M.NewBoolVar(f'{nombre}_ig{i}')
        M.Add(a[i] == b[i]).OnlyEnforceIf(iguales)
        M.Add(a[i] != b[i]).OnlyEnforceIf(iguales.Not())
        M.AddBoolAnd([eq[i], iguales]).OnlyEnforceIf(eq[i + 1])
        M.AddBoolOr([eq[i].Not(), iguales.Not(), eq[i + 1]])
        M.AddImplication(eq[i + 1], eq[i])
        M.AddImplication(eq[i + 1], iguales)


def modelo_dlex(m, n, z):
    M, y, x = modelo(m, n, z=z)
    filas = [[y[(i, j)] for j in range(n)] for i in range(m)]
    cols = [[y[(i, j)] for i in range(m)] for j in range(n)]
    for i in range(m - 1):
        lex_ge(M, filas[i], filas[i + 1], f'f{i}')
    for j in range(n - 1):
        lex_ge(M, cols[j], cols[j + 1], f'c{j}')
    return M, y, x


if __name__ == '__main__':
    m, n = int(sys.argv[1]), int(sys.argv[2])
    seg = int(sys.argv[sys.argv.index('--seg') + 1]) if '--seg' in sys.argv else 1800
    t0 = time.time()
    z = z_de(m, n)
    M, y, x = modelo_dlex(m, n, z)
    M.Maximize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = seg
    s.parameters.num_workers = 4
    if '--simetria-cpsat' in sys.argv:
        s.parameters.symmetry_level = 4
    st = s.StatusName(s.Solve(M))
    v = int(s.ObjectiveValue())
    print(f'dlex z_L({m},{n}) = {z + v}  (z = {z}, |E2| = {v}, cota {int(s.BestObjectiveBound())}) {st}  '
          f'[{time.time() - t0:.1f} s]', flush=True)
