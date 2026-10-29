# Admissibility checker of Definition 2.1 (both readings of (C3)); exact small values as controls.
"""python zl.py — controles (valores exactos del artículo) y z_L(5,5) con las DOS lecturas de la condición 3.

Def. 2.1 (v5): E1 ⊆ [m]×[n] sin C4 con |E1| = z(m,n); E2 = conjunto de 2-aristas, cada una un par no ordenado de
celdas distintas {(i,j),(p,q)} (no degenerada si i≠p y j≠q; fila-degenerada si i=p; columna-degenerada si j=q).
(S) Las mitades de las 2-aristas no son 1-aristas y no se comparten. Ocupada = 1-arista o mitad de alguna 2-arista.
Violación (C4 generalizado):
  1. C4 de 1-aristas (no ocurre: E1 sin C4 por construcción);
  2. 2-arista NO degenerada (i,j;p,q) con (i,q) y (p,j) ambas ocupadas;
  3. 2-arista (i,j;p,q) y (k,l) con k∉{i,p}, l∉{j,q} y las cinco celdas (k,l),(k,j),(k,q),(i,l),(p,l) ocupadas;
     «si la 2-arista es no degenerada, las cinco deben ser distintas por pares».
Lectura A (apéndice C): en una degenerada las repetidas cuentan → la condición 3 se aplica a TODAS las 2-aristas.
Lectura B (apéndice B.4): en una degenerada la configuración con repetidas «no constituye» violación → la condición 3
solo se aplica a las NO degeneradas.
z_L(m,n) = máx |E1| + |E2|. Monotonía: añadir 2-aristas solo añade celdas ocupadas, así que si un conjunto viola, todo
superconjunto viola → búsqueda en profundidad con poda."""
import itertools
import sys
import time


def popcount(x):
    return bin(x).count('1')


def zarankiewicz_y_bases(m, n):
    """(z, lista de E1 extremales salvo permutación de filas y columnas). Filas = máscaras de n bits."""
    mejor, bases = -1, set()
    perms = list(itertools.permutations(range(n)))

    def perm_mask(r, p):
        return sum(1 << p[b] for b in range(n) if r >> b & 1)

    def canon(filas):
        return min(tuple(sorted(perm_mask(r, p) for r in filas)) for p in perms)

    def rec(filas, desde):
        nonlocal mejor, bases
        if len(filas) == m:
            t = sum(popcount(r) for r in filas)
            if t > mejor:
                mejor, bases = t, set()
            if t == mejor:
                bases.add(canon(filas))
            return
        for r in range(desde, 1 << n):
            if all(popcount(r & s) <= 1 for s in filas):
                rec(filas + [r], r)
    rec([], 0)
    return mejor, sorted(bases)


def celdas_e1(filas, n):
    return {(i, j) for i, r in enumerate(filas) for j in range(n) if r >> j & 1}


def viola(E1, E2, m, n, lectura):
    ocup = set(E1)
    mitades = set()
    for a, b in E2:
        if a in E1 or b in E1 or a in mitades or b in mitades:
            return True  # (S)
        mitades |= {a, b}
    ocup |= mitades
    for (i, j), (p, q) in E2:
        nodeg = i != p and j != q
        if nodeg and (i, q) in ocup and (p, j) in ocup:
            return True  # condición 2
        if lectura == 'B' and not nodeg:
            continue
        for k in range(m):
            if k in (i, p):
                continue
            for l in range(n):
                if l in (j, q):
                    continue
                if all(c in ocup for c in ((k, l), (k, j), (k, q), (i, l), (p, l))):
                    return True  # condición 3
    return False


def max_e2(E1, m, n, lectura):
    U = [(i, j) for i in range(m) for j in range(n) if (i, j) not in E1]
    cands = [(a, b) for a, b in itertools.combinations(U, 2) if not viola(E1, [(a, b)], m, n, lectura)]
    mejor = [0, []]

    def dfs(sel, desde, usadas):
        if len(sel) > mejor[0]:
            mejor[0], mejor[1] = len(sel), list(sel)
        if len(sel) + (len(U) - len(usadas)) // 2 <= mejor[0]:
            return  # cota: cada 2-arista usa 2 celdas libres
        for t in range(desde, len(cands)):
            a, b = cands[t]
            if a in usadas or b in usadas:
                continue
            nuevo = sel + [cands[t]]
            if not viola(E1, nuevo, m, n, lectura):
                dfs(nuevo, t + 1, usadas | {a, b})
    dfs([], 0, frozenset())
    return mejor[0], mejor[1]


def zl(m, n, lectura):
    z, bases = zarankiewicz_y_bases(m, n)
    res = []
    for filas in bases:
        E1 = celdas_e1(filas, n)
        k, ej = max_e2(E1, m, n, lectura)
        res.append((k, filas, ej))
    kmax = max(r[0] for r in res)
    return z, len(bases), z + kmax, [r for r in res if r[0] == kmax][:1]


if __name__ == '__main__':
    casos = [(5, 3, 9), (5, 4, 12), (6, 4, 14), (4, 3, 8), (4, 4, 10), (3, 3, 6)]
    for lectura in ('A', 'B'):
        print(f'== lectura {lectura}')
        for m, n, esperado in casos:
            t0 = time.time()
            z, nb, v, ej = zl(m, n, lectura)
            print(f'  z_L({m},{n}) = {v}  (z = {z}, {nb} bases)  artículo: {esperado}  '
                  f"{'OK' if v == esperado else 'DISTINTO'}  [{time.time() - t0:.1f} s]", flush=True)
    # testigo publicado de z_L(5,5) ≥ 15 (filas y columnas 1..5 → 0..4)
    E1 = {(r - 1, c - 1) for r, c in [(1, 1), (1, 4), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1), (5, 3), (5, 5)]}
    E2 = [((0, 1), (2, 4)), ((1, 2), (3, 3)), ((2, 0), (4, 3))]
    for lectura in ('A', 'B'):
        print(f'testigo de 15 en 5×5, lectura {lectura}: admisible =', not viola(E1, E2, 5, 5, lectura))
    if '--55' in sys.argv:
        for lectura in ('A',):  # la B no reproduce los valores exactos del artículo (5 de 6 distintos)
            t0 = time.time()
            z, nb, v, ej = zl(5, 5, lectura)
            print(f'z_L(5,5) lectura {lectura} = {v}  (z = {z}, {nb} bases; ejemplo {ej})  [{time.time() - t0:.0f} s]', flush=True)
