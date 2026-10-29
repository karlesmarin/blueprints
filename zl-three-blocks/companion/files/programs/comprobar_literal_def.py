# Second, independent admissibility checker: Definition 2.1 read literally, cell by cell.
import itertools
import json
import os

AQUI = os.path.dirname(os.path.abspath(__file__))


def generalized_c4(E1, E2, m, n):
    """Devuelve la primera razón por la que G contiene un generalized C4-cycle, o None. Texto:
    (S) No 2-edge shares a cell (i,j) with any 1-edge or with another 2-edge.
    occupied: (i,j) in E1 or a half of some 2-edge.
    C1: classical C4 formed by 1-edges.
    C2: nondegenerate 2-edge (i,j;k,l) with both opposite cells (i,l) and (k,j) occupied.
    C3: a 2-edge (i,j;p,q) (of any type) and a distinct cell (k,l), k not in {i,p}, l not in {j,q}, such that the five
        cells (k,l),(k,j),(k,q),(i,l),(p,l) are all occupied; if the 2-edge is nondegenerate, the five cells must be
        pairwise distinct."""
    halves = [h for e in E2 for h in e]
    for (i, j), (k, l) in E2:  # una 2-arista son dos celdas distintas
        if (i, j) == (k, l):
            return 'S: 2-arista con dos mitades iguales'
    if len(set(halves)) != len(halves):
        return 'S: dos 2-aristas comparten celda'
    if set(halves) & set(E1):
        return 'S: una mitad es 1-arista'
    occupied = set(E1) | set(halves)
    for r1, r2 in itertools.combinations(range(m), 2):
        for c1, c2 in itertools.combinations(range(n), 2):
            if {(r1, c1), (r1, c2), (r2, c1), (r2, c2)} <= set(E1):
                return f'C1 en filas {r1},{r2} columnas {c1},{c2}'
    for (i, j), (k, l) in E2:
        if i != k and j != l and (i, l) in occupied and (k, j) in occupied:
            return f'C2 en {(i, j)}-{(k, l)}'
    for (i, j), (p, q) in E2:
        nondeg = i != p and j != q
        for k in range(m):
            for l in range(n):
                if k in (i, p) or l in (j, q):
                    continue
                five = [(k, l), (k, j), (k, q), (i, l), (p, l)]
                if all(c in occupied for c in five) and (not nondeg or len(set(five)) == 5):
                    return f'C3 con {(i, j)}-{(p, q)} y celda {(k, l)}'
    return None


if __name__ == '__main__':
    t = json.load(open(os.path.join(AQUI, 'testigo_10_5.json')))
    E1 = [tuple(c) for c in t['E1']]
    E2 = [(tuple(a), tuple(b)) for a, b in t['E2']]
    print('testigo 10×5, |E1| =', len(E1), '|E2| =', len(E2), '→', generalized_c4(E1, E2, 10, 5) or 'SIN generalized C4: ADMISIBLE')
    # controles: el testigo publicado de 15 en 5×5 (admisible) y dos rupturas sembradas (deben dar razón)
    T1 = [(r - 1, c - 1) for r, c in [(1, 1), (1, 4), (2, 2), (2, 4), (2, 5), (3, 2), (3, 3), (4, 1), (4, 2), (5, 1), (5, 3), (5, 5)]]
    T2 = [((0, 1), (2, 4)), ((1, 2), (3, 3)), ((2, 0), (4, 3))]
    print('control + (publicado 15 en 5×5):', generalized_c4(T1, T2, 5, 5) or 'ADMISIBLE')
    print('control − (mitad sobre 1-arista):', generalized_c4(E1, E2 + [((0, 0), (9, 0))], 10, 5))
    print('control − (C2 sembrado):', generalized_c4(T1, T2 + [((0, 2), (3, 4))], 5, 5))
    # su construcción de 23 (e1, e2, e3 en etiquetas de K5) también debe ser admisible: la rehacemos en nuestras coordenadas
