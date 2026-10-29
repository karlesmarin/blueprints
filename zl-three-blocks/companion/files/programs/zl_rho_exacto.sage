# Theorems C and D, n <= 5: the slopes by exact linear programming in Sage.
import itertools
import sys

n = int(sys.argv[1])
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
            if S & T == frozenset([j]):
                aristas.append(((S, j), (T, q)))
            continue
        if q in S and j in T:
            continue
        if any(frozenset((j, q, l)) in H for l in (S & T) - {j, q}):
            continue
        aristas.append(((S, j), (T, q)))
    return Sl, ports, aristas


def valor(H, canonica):
    Sl, ports, aristas = estructura(H)
    if not aristas:
        return QQ(0)
    p = MixedIntegerLinearProgram(maximization=True, solver='PPL')
    x = p.new_variable(nonnegative=True)
    y = p.new_variable(nonnegative=True)
    xs = [(S, b) for S in Sl for b in S if (b == 0 or not canonica)]
    p.add_constraint(p.sum(x[(tuple(sorted(S)), b)] for (S, b) in xs) <= 1)
    ie = {e: k for k, e in enumerate(aristas)}
    for (S, j) in ports:
        cap = [x[(tuple(sorted(S)), b)] for b in S if b != j and (S, b) in xs]
        dem = [y[ie[e]] for e in aristas if (S, j) in e]
        if dem:
            p.add_constraint(p.sum(dem) <= (p.sum(cap) if cap else 0))
    p.set_objective(p.sum(y[k] for k in range(len(aristas))))
    return QQ(p.solve())


mejor = {True: QQ(0), False: QQ(0)}
for mask in range(1 << len(TR)):
    H = set(TR[i] for i in range(len(TR)) if mask >> i & 1)
    for can in (True, False):
        mejor[can] = max(mejor[can], valor(H, can))
print('n = %d: rho exacto = %s ; canonica exacta = %s' % (n, mejor[False], mejor[True]))
