# Section 7: F_n(m) exactly by the integer program over row types (CP-SAT).
"""python zl_tipos.py n m1 m2 [--seg 600]"""
import itertools
import sys

from ortools.sat.python import cp_model


def F(n, m, seg=600):
    C = range(n)
    pares = [frozenset(p) for p in itertools.combinations(C, 2)]
    t = m - len(pares)
    assert t >= 0
    M = cp_model.CpModel()
    tipos = []  # (base, soporte, var de conteo)
    for a in C:
        for k in range(0, n):
            for resto in itertools.combinations([c for c in C if c != a], k):
                S = frozenset((a,) + resto)
                tipos.append((frozenset((a,)), S, M.NewIntVar(0, t, '')))
    M.Add(sum(v for B, S, v in tipos if len(B) == 1) == t)
    for P in pares:
        opc = []
        for k in range(0, n - 1):
            for resto in itertools.combinations([c for c in C if c not in P], k):
                v = M.NewBoolVar('')
                tipos.append((P, P | frozenset(resto), v))
                opc.append(v)
        M.Add(sum(opc) == 1)
    triples = [frozenset(x) for x in itertools.combinations(C, 3)]
    Mt = {T: sum(v for B, S, v in tipos if T <= S) for T in triples}
    BIG = m + 3
    ge = {}
    for T in triples:
        for k in (1, 2, 3):
            b = M.NewBoolVar('')
            M.Add(Mt[T] - (k - 1) <= BIG * b)
            ge[(T, k)] = b
    puertos = {}
    for idx, (B, S, v) in enumerate(tipos):
        for j in S - B:
            puertos[(idx, j)] = []
    total = []
    # pares entre filas de tipos distintos
    for (i1, j), (i2, q) in itertools.combinations(list(puertos), 2):
        if i1 == i2:
            continue
        S, T = tipos[i1][1], tipos[i2][1]
        if j == q:
            if S & T != {j}:
                continue
            bloq = []
        else:
            if q in S and j in T:
                continue
            bloq = []
            for l in (S & T) - {j, q}:
                Tr = frozenset((j, q, l))
                c = int(Tr <= S) + int(Tr <= T)
                bloq.append(ge[(Tr, c + 1)])
        f = M.NewIntVar(0, t + 1, '')
        for b in bloq:
            M.Add(f <= BIG * (1 - b))
        puertos[(i1, j)].append(f)
        puertos[(i2, q)].append(f)
        total.append(f)
    # pares horizontales dentro de una fila
    for idx, (B, S, v) in enumerate(tipos):
        ext = sorted(S - B)
        hs = []
        for j, q in itertools.combinations(ext, 2):
            h = M.NewIntVar(0, t + 1, '')
            for l in S - {j, q}:
                M.Add(h <= BIG * (1 - ge[(frozenset((j, q, l)), 2)]))
            puertos[(idx, j)].append(h)
            puertos[(idx, q)].append(h)
            hs.append(h)
            total.append(h)
        if hs:
            M.Add(sum(hs) <= v)
    for (idx, j), lst in puertos.items():
        M.Add(sum(lst) == tipos[idx][2])
    M.Maximize(sum(total))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = seg
    s.parameters.num_workers = 4
    st = s.StatusName(s.Solve(M))
    return st, int(s.ObjectiveValue()), int(s.BestObjectiveBound())


if __name__ == '__main__':
    n, m1, m2 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seg = int(sys.argv[sys.argv.index('--seg') + 1]) if '--seg' in sys.argv else 600
    for m in range(m1, m2 + 1):
        st, v, b = F(n, m, seg)
        extra = ''
        if n == 3:
            extra = f' (fórmula {(m - 2) // 2})'
        if n == 4:
            fo = 2 if m == 6 else max((3 * m - 12) // 4, (2 * m - 3) // 3)
            extra = f' (closed formula {fo})'
        print(f'n = {n}, m = {m}: F = {v} {st} (cota {b}){extra}', flush=True)
