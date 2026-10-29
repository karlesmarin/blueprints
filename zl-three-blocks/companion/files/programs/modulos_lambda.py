# Theorem B, lower bound: the three-block modules for n = 3..12, checked by both checkers.
import itertools
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from comprobar_literal_def import generalized_c4  # noqa: E402
from zl import viola  # noqa: E402


def lam(n):
    r = n % 3
    if r == 0:
        return Fraction(2 * n - 3, 6)
    if r == 1:
        return Fraction((n - 1) * (2 * n - 5), 6 * (n - 2))
    return Fraction((n - 2) * (2 * n - 1), 6 * (n - 1))


def bloques(n):
    b, r = divmod(n, 3)
    tam = {0: (b, b, b), 1: (b + 1, b, b), 2: (b + 1, b + 1, b)}[r]
    out, c = [], 0
    for t in tam:
        out.append(list(range(c, c + t)))
        c += t
    return out, r


def modulo(n):
    """Lista de (tipo como par de índices de bloque, bloque de la celda de E1) por módulo."""
    Bl, r = bloques(n)
    if r in (0, 1):  # tamaños (B, c, c)
        B, c = len(Bl[0]), len(Bl[1])
        return [((0, 1), 0)] * (2 * c - 1) + [((0, 2), 0)] * (2 * c - 1) + [((1, 2), 1)] * (B - 1) + \
            [((1, 2), 2)] * (B - 1), (2 * c - 1) * (2 * B + c - 2)
    B, c = len(Bl[0]), len(Bl[2])  # tamaños (B, B, c)
    return [((0, 1), 0)] * c + [((0, 1), 1)] * c + [((0, 2), 0)] * (2 * B - 1) + [((1, 2), 1)] * (2 * B - 1), \
        (2 * B - 1) * (B + 2 * c - 1)


def construir(n, q):
    Bl, _ = bloques(n)
    blo = {c: i for i, X in enumerate(Bl) for c in X}
    mod, ppm = modulo(n)
    filas = []  # (cols E1, tipo)
    for p in itertools.combinations(range(n), 2):
        filas.append((list(p), None))
    for _ in range(q):
        for tipo, bb in mod:
            filas.append(([Bl[bb][0]], tipo))
    m = len(filas)
    E1 = {(i, c) for i, (cs, _) in enumerate(filas) for c in cs}
    ext = {}
    for i, (cs, tipo) in enumerate(filas):
        if tipo is None:
            continue
        for x in tipo:
            for c in Bl[x]:
                if c not in cs:
                    ext.setdefault((tipo, x), []).append((i, c))
    E2 = []
    for i, j in itertools.combinations(range(3), 2):
        k = 3 - i - j
        for comun in (i, j, k):
            pass
    # canales: puerto (T, x) con x ∈ T∖T' empareja con (T', y), y ∈ T'∖T, T = {x, z}, T' = {z, y}
    usados = set()
    for z in range(3):
        x, y = [w for w in range(3) if w != z]
        T, T2 = tuple(sorted((x, z))), tuple(sorted((z, y)))
        a, b = ext.get((T, x), []), ext.get((T2, y), [])
        for u, v in zip(a, b):
            E2.append((u, v))
    return m, E1, E2, ppm, len(mod)


ok_todo = True
for n in range(3, 13):
    for q in (1, 2):
        m, E1, E2, ppm, rpm = construir(n, q)
        adm = not generalized_c4(sorted(E1), E2, m, n) and not viola(set(E1), E2, m, n, 'A')
        ok = adm and len(E2) == q * ppm and Fraction(ppm, rpm) == lam(n) and len(E1) == m + n * (n - 1) // 2
        ok_todo &= ok
        print(f'n = {n}, q = {q}: m = {m}, |E1| = {len(E1)}, |E2| = {len(E2)} (esperado {q * ppm}), '
              f'módulo {ppm}/{rpm} = {Fraction(ppm, rpm)} (λ = {lam(n)}), admisible {adm} → {"OK" if ok else "FALLA"}',
              flush=True)
print('TODO OK' if ok_todo else 'HAY FALLOS')
