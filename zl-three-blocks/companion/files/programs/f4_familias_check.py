# Theorem E, lower bound: the two periodic families (data/F4_families.json) checked by both checkers, profile per residue.
"""python f4_familias_check.py ../data/F4_families.json [M]"""
import importlib.util
import itertools
import json
import sys
from types import SimpleNamespace

from comprobar_literal_def import generalized_c4
from zl import viola


def desde_json(ruta):
    """Las familias como DATOS (F4_families.json, índices desde 1): semilla por clase de restos + módulo repetido."""
    d = json.load(open(ruta, encoding='utf-8'))

    def filas_pares(rows, pairs, r=0):
        return ([{j - 1 for j in x} for x in rows],
                [((r + i - 1, j - 1), (r + p - 1, q - 1)) for (i, j), (p, q) in pairs])

    def familia(fam):
        def construir(m):
            b = fam['from'] + (m - fam['from']) % fam['period']
            s = fam['seeds'][str(b)]
            T, E = filas_pares(s['rows'], s['pairs'])
            while len(T) < m:
                t, e = filas_pares(s['module_rows'], s['module_pairs'], len(T))
                T, E = T + t, E + e
            return T, E
        return construir

    dos, tres = familia(d['two_thirds']), familia(d['three_quarters'])

    def construct(m):
        if m == 6:
            return filas_pares(d['m6']['rows'], d['m6']['pairs'])
        if m >= 10 and (3 * m - 12) // 4 >= (2 * m - 3) // 3:
            return tres(m)
        return dos(m)
    return SimpleNamespace(construct=construct, family_two_thirds=dos, family_three_quarters=tres)


if sys.argv[1].endswith('.json'):
    cc = desde_json(sys.argv[1])
else:
    sys.exit('give the families as data: ../data/F4_families.json')
M = int(sys.argv[2]) if len(sys.argv) > 2 else 200
TR = list(itertools.combinations(range(4), 3))


def perfil(T, E):
    sup = [set(s) for s in T]
    for (i, j), (p, q) in E:
        sup[i].add(j)
        sup[p].add(q)
    return tuple(min(2, sum(1 for s in sup if set(U) <= s)) for U in TR)


malos, perf = [], {}
for m in range(6, M + 1):
    T, E = cc.construct(m)
    E1 = {(i, j) for i, s in enumerate(T) for j in s}
    ok_base = len(T) == m and len(E1) == m + 6 and all(len(T[i] & T[p]) <= 1 for i, p in itertools.combinations(range(m), 2))
    objetivo = 2 if m == 6 else max((2 * m - 3) // 3, (3 * m - 12) // 4)
    lit = generalized_c4(sorted(E1), E, m, 4)
    va = viola(E1, E, m, 4, 'A')
    perf[m] = perfil(T, E)
    if not ok_base or len(E) != objetivo or lit or va:
        malos.append((m, ok_base, len(E), objetivo, lit, va))
print(f'm = 6..{M}: fallos {malos[:5]} (total {len(malos)})')
# periodicidad del perfil: cada familia repite un módulo; el perfil debe estabilizarse por clase de residuos
for fam, per, ini in (('dos tercios', 3, 7), ('tres cuartos', 4, 10)):
    f = cc.family_two_thirds if per == 3 else cc.family_three_quarters
    est = {}
    for m in range(ini + 3 * per, M + 1):
        est.setdefault(m % per, set()).add(perfil(*f(m)))
    print(f'familia {fam}: perfiles por residuo (m >= {ini + 3 * per}):', {r: sorted(s) for r, s in est.items()})
