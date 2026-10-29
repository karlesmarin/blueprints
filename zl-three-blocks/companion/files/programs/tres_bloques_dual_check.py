# Proposition 6.3: weights, row budgets, modules and the maximum lambda_n in exact arithmetic, every partition with n <= 60.
import sys
from fractions import Fraction as Q

N = int(sys.argv[1]) if len(sys.argv) > 1 else 60


def lam(n):
    r = n % 3
    return Q(2 * n - 3, 6) if r == 0 else (Q((n - 1) * (2 * n - 5), 6 * (n - 2)) if r == 1 else Q((n - 2) * (2 * n - 1), 6 * (n - 1)))


fallos = []
for n in range(3, N + 1):
    mejor, arg = None, []
    for a in range(1, n):
        for b in range(1, a + 1):
            c = n - a - b
            if c < 1 or c > b:
                continue
            caso1 = c * (a - 1) >= b * (b - 1)
            if caso1:
                s = b + c
                M = Q((s - 1) * ((a - 1) * s + b * c), s * (n - 2))
                x = z = Q(s * (s - 1) - b * c, s * (n - 2))
                y = Q(c, s)
                filas = {('AB', 'A'): c * (s - 1), ('AC', 'A'): b * (s - 1), ('BC', 'B'): (a - 1) * b, ('BC', 'C'): (a - 1) * c}
            else:
                t = a + b - 2
                M = Q((t + 1) * (c * t + (a - 1) * (b - 1)), t * (n - 1))
                x = y = Q(c * t + (a - 1) * (b - 1), t * (n - 1))
                z = Q(b - 1, t)
                filas = {('AB', 'A'): c * (b - 1), ('AB', 'B'): c * (a - 1), ('AC', 'A'): (b - 1) * (t + 1), ('BC', 'B'): (a - 1) * (t + 1)}
            tam = {'A': a, 'B': b, 'C': c}
            # pesos por (tipo, bloque del extremo)
            W = {('AB', 'A'): x, ('AB', 'B'): y, ('AC', 'A'): z, ('AC', 'C'): 1 - y, ('BC', 'B'): 1 - z, ('BC', 'C'): 1 - x,
                 ('A', 'A'): max(x, z), ('B', 'B'): max(y, 1 - z), ('C', 'C'): max(1 - x, 1 - y)}
            ok = all(0 <= w <= 1 for w in W.values())
            tipos = ['AB', 'AC', 'BC', 'A', 'B', 'C']
            # parejas recíprocas: extremo de T en X ∈ T∖T', de T' en Y ∈ T'∖T
            for T in tipos:
                for T2 in tipos:
                    for X in set(T) - set(T2):
                        for Y in set(T2) - set(T):
                            if W[(T, X)] + W[(T2, Y)] < 1:
                                ok = False
            # coste de fila: ancla en cualquier bloque del tipo; el resto de celdas del tipo son extremos (como mucho)
            for T in tipos:
                for anc in T:
                    coste = sum(W[(T, X)] * (tam[X] - (1 if X == anc else 0)) for X in T)
                    if coste > M:
                        ok = False
            # primal: extremos por (tipo, bloque) y canales
            ext = {}
            for (T, anc), r in filas.items():
                for X in T:
                    ext[(T, X)] = ext.get((T, X), 0) + r * (tam[X] - (1 if X == anc else 0))
            canales = [(('AB', 'A'), ('BC', 'C')), (('AB', 'B'), ('AC', 'C')), (('AC', 'A'), ('BC', 'B'))]
            P = 0
            for u, v in canales:
                if ext.get(u, 0) != ext.get(v, 0):
                    ok = False
                P += ext.get(u, 0)
            R = sum(filas.values())
            if R == 0 or Q(P, R) != M:
                ok = False
            if not ok:
                fallos.append((n, a, b, c))
            if mejor is None or M > mejor:
                mejor, arg = M, [(a, b, c)]
            elif M == mejor:
                arg.append((a, b, c))
    if mejor != lam(n) or any(max(t) - min(t) > 1 for t in arg):
        fallos.append(('max', n, mejor, lam(n), arg))
print(f'n = 3..{N}: particiones comprobadas; fallos: {fallos[:5]} (total {len(fallos)})')
