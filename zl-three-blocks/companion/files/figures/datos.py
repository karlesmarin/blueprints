# Data of the figures: rebuilds the witnesses and passes them again through both checkers.
import itertools
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ZL = Path(__file__).resolve().parents[1] / 'programs'
sys.path.insert(0, str(ZL))
from comprobar_literal_def import generalized_c4  # noqa: E402
from zl import viola  # noqa: E402


def tres_bloques_22x5():
    """Óptimo de tres bloques 22×5 (A={0,1}, B={2,3}, C={4}): filas especiales + 6 singleton en col 0 + 6 en col 2;
    soporte ocupado de cada fila = unión de dos bloques; pares por la regla cruzada. Devuelve (m, n, E1, E2, bloque
    evitado por fila)."""
    n, bl = 5, [{0, 1}, {2, 3}, {4}]
    A, B, C = bl
    filas = []
    for p in itertools.combinations(range(n), 2):
        s = set(p)
        filas.append((p, A | B if s <= A | B else (A | C if s & A else B | C)))
    filas += [((0,), A | C)] * 6 + [((2,), B | C)] * 6
    E1, ext, evita = set(), {}, []
    for r, (orig, ocup) in enumerate(filas):
        E1 |= {(r, c) for c in orig}
        t = next(i for i in range(3) if not (ocup & bl[i]))
        evita.append(t)
        for c in sorted(ocup - set(orig)):
            j = next(i for i in range(3) if c in bl[i])
            ext.setdefault((t, j), []).append((r, c))
    E2 = []
    for i, j in itertools.combinations(range(3), 2):
        E2 += list(zip(sorted(ext[(i, j)]), sorted(ext[(j, i)])))
    m = len(filas)
    assert not generalized_c4(sorted(E1), E2, m, n) and not viola(E1, E2, m, n, 'A')
    assert len(E1) == 32 and len(E2) == 20
    return m, n, E1, E2, evita


def tensor_3x3x5():
    """The 3D counterexample of Proposition 8.1: indices from 0."""
    U = {(0, 2, 2), (1, 2, 3), (2, 0, 0), (2, 1, 2), (2, 2, 4)}
    P = [((0, 0, 2), (1, 0, 4)), ((0, 1, 0), (2, 0, 3)), ((0, 1, 1), (1, 2, 1))]
    celdas = set(itertools.product(range(3), range(3), range(5)))
    ext = {c for p in P for c in p}
    E1 = celdas - U - ext
    O = celdas - U

    def caja(a, b):
        return set(itertools.product(*({a[k], b[k]} for k in range(3))))
    assert not any(all(a[k] != b[k] for k in range(3)) and caja(a, b) <= E1
                   for a, b in itertools.combinations(sorted(E1), 2))
    for a, b in P:
        na = {d for d in O if all(a[k] != d[k] for k in range(3)) and caja(a, d) <= O}
        nb = {d for d in O if all(b[k] != d[k] for k in range(3)) and caja(b, d) <= O}
        assert b not in na and not (na & nb)
    assert len(E1) == 34
    return E1, P, U


def lam(n):
    r = n % 3
    if r == 0:
        return Fraction(2 * n - 3, 6)
    if r == 1:
        return Fraction((n - 1) * (2 * n - 5), 6 * (n - 2))
    return Fraction((n - 2) * (2 * n - 1), 6 * (n - 1))


def pendientes():
    """(n, λ_n, estado) para n = 3..12; estado: 'certificado' (n ≤ 6, cert_sombras_n.json), 'calculado' (n = 7, MIP),
    'cota inferior' (resto)."""
    out = []
    for n in range(3, 13):
        if n <= 6:
            d = json.load(open(ZL / f'cert_sombras_{n}.json'))
            assert Fraction(*d['cota']) == lam(n)
            est = 'certificado'
        elif n == 7:
            est = 'calculado'
        else:
            est = 'cota inferior'
        out.append((n, lam(n), est))
    return out


def f4():
    """F_4(m) exacto para m = 6..40: tablas fila a fila (m ≤ 14) y reducción por tipos (zl_tipos_n4.log)."""
    vals = {}
    for linea in (ZL / 'zl_tipos_n4.log').read_text(encoding='utf-8').splitlines():
        mt = re.search(r'm = (\d+): F = (\d+) OPTIMAL', linea)
        if mt:
            vals[int(mt.group(1))] = int(mt.group(2))
    for d in map(json.loads, (ZL / 'tabla_zl_nauty.jsonl').read_text(encoding='utf-8').splitlines()):
        if d['n'] == 4 and d['m'] >= 6 and d['exacto']:
            vals[d['m']] = d['zl'] - d['z']
    return dict(sorted(vals.items()))


PUBLICADOS = {(3, 3), (4, 3), (4, 4), (5, 3), (5, 4), (6, 4), (5, 5), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6),
              (7, 7), (10, 5), (6, 3), (8, 3), (9, 3), (10, 3), (11, 3), (12, 3), (13, 3)}


def tabla():
    """{(m, n): (z_L, 'publicado'|'nuevo'|'cota', cota_sup)} de las tablas exactas propias."""
    out = {}
    for f in ('tabla_zl_dlex.jsonl', 'tabla_zl_nauty.jsonl'):
        for d in map(json.loads, (ZL / f).read_text(encoding='utf-8').splitlines()):
            exacto = d.get('exacto', d.get('estado') == 'OPTIMAL')
            sup = d.get('cota_sup', d['zl'])
            clave = (d['m'], d['n'])
            if clave in out and out[clave][1] != 'cota':
                continue
            out[clave] = (d['zl'], ('publicado' if clave in PUBLICADOS else 'nuevo') if exacto else 'cota', sup)
    return out


if __name__ == '__main__':
    m, n, E1, E2, ev = tres_bloques_22x5()
    print('22×5:', m, n, len(E1), len(E2))
    print('3D:', len(tensor_3x3x5()[0]))
    print('pendientes:', [(a, str(b), c) for a, b, c in pendientes()])
    print('F4:', f4())
    t = tabla()
    print('tabla:', len(t), 'tamaños;', sum(1 for v in t.values() if v[1] == 'nuevo'), 'nuevos')
