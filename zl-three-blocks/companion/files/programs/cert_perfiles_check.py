# Independent checker of the 29 profile certificates: rebuilds types, ports and permitted pairs from scratch.
"""python cert_perfiles_check.py n carpeta   (lee lp_<a>_<b>_<k>.json solo para las claves y cert_lp_*.json para los multiplicadores)"""
import itertools
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

n = int(sys.argv[1])
carpeta = Path(sys.argv[2])
cols = list(range(n))
triples = [tuple(t) for t in itertools.combinations(cols, 3)]
pares = [tuple(p) for p in itertools.combinations(cols, 2)]


def matchings(xs):
    xs = list(xs)
    if not xs:
        return [[]]
    a, rest = xs[0], xs[1:]
    out = [m for m in matchings(rest)]
    for i, b in enumerate(rest):
        out += [[(a, b)] + m for m in matchings(rest[:i] + rest[i + 1:])]
    return out


def tipos_de(perf):
    res = []
    for B in [(a,) for a in cols] + pares:
        libres = [c for c in cols if c not in B]
        for r in range(len(libres) + 1):
            for ex in itertools.combinations(libres, r):
                S = tuple(sorted(B + ex))
                if any(perf[t] == 0 for t in triples if set(t) <= set(S)):
                    continue
                for M in matchings([c for c in S if c not in B]):
                    if all(perf[tuple(sorted((j, q, l)))] == 1 for (j, q) in M for l in S if l not in (j, q)):
                        res.append((B, S, tuple(M)))
    return res


def arista_ok(S, j, T, q, perf):
    S, T = set(S), set(T)
    if j == q:
        return S & T == {j}
    if q in S and j in T:
        return False
    for l in (S & T) - {j, q}:
        U = tuple(sorted((j, q, l)))
        if perf[U] >= 1 + (set(U) <= S) + (set(U) <= T):
            return False
    return True


def clave_tipo(t):
    B, S, M = t
    return json.dumps([sorted(B), sorted(S), sorted(sorted(x) for x in M)])


# órbitas de perfiles (recalculadas)
todos = set(itertools.product((0, 1, 2), repeat=len(triples)))
cubiertos = set()
resultados = {}
for lpf in sorted(carpeta.glob('lp_*.json')):
    certf = lpf.with_name('cert_' + lpf.name)
    lp = json.load(open(lpf))
    v = tuple(lp['perfil'])
    a, b = lp['alfa'], lp['beta']
    perf = dict(zip(triples, v))
    if not certf.exists():
        resultados.setdefault(v, {})[(a, b)] = None  # sin certificado (dual infactible: la cota no vale para este perfil)
        continue
    cert = json.load(open(certf))
    mult = {}
    for keys, vals, signo in ((lp['eq_keys'], cert['u'], 1), (lp['ge_keys'], cert['v'], -1), (lp['le_keys'], cert['w'], 1)):
        for k, (x, y) in zip(keys, vals):
            mult[json.dumps(k)] = (signo, Q(x, y))
    T = tipos_de(perf)
    ports = [(t, j) for t in T for j in t[1] if j not in t[0] and all(j not in par for par in t[2])]
    claves_esperadas = {json.dumps(['par', list(p)]) for p in pares} | {json.dumps(['singleton']), json.dumps(['llena'])}
    claves_esperadas |= {json.dumps(['puerto', json.loads(clave_tipo(t)), j]) for t, j in ports}
    claves_esperadas |= {json.dumps(['triple', list(U)]) for U in triples}
    assert claves_esperadas == set(mult), ('claves', v)

    def m_(k):
        s, x = mult[json.dumps(k)]
        return s * x
    for x in mult.values():
        assert x[0] == 1 or x[1] >= 0  # v, w >= 0 (los de ≥ entran con signo −)
    for k in mult:
        if json.loads(k)[0] in ('llena',) or (json.loads(k)[0] == 'triple' and perf[tuple(json.loads(k)[1])] == 2):
            assert mult[k][1] >= 0
    comprob = 0
    for t in T:
        B, S, M = t
        tot = Q(0)
        if len(B) == 2:
            tot += m_(['par', list(B)])
        else:
            tot += m_(['singleton'])
        tot -= sum((m_(['puerto', json.loads(clave_tipo(t)), j]) for tt, j in ports if tt == t), Q(0))
        tot += sum((m_(['triple', list(U)]) for U in triples if set(U) <= set(S)), Q(0))
        if len(S) == n:
            tot += m_(['llena'])
        assert tot >= a * len(M), ('columna tipo', t, tot)
        comprob += 1
    for (i, pa), (k, pb) in itertools.combinations(enumerate(ports), 2):
        if pa[0] != pb[0] and arista_ok(pa[0][1], pa[1], pb[0][1], pb[1], perf):
            s = m_(['puerto', json.loads(clave_tipo(pa[0])), pa[1]]) + m_(['puerto', json.loads(clave_tipo(pb[0])), pb[1]])
            assert s >= a, ('columna arista', pa, pb, s)
            comprob += 1
    assert -m_(['singleton']) >= -b, 'columna m'
    valor = sum((m_(['par', list(p)]) for p in pares), Q(0)) + m_(['singleton']) * (-len(pares))
    valor += sum((m_(['triple', list(U)]) * (2 if perf[U] == 2 else perf[U]) for U in triples), Q(0))
    valor += m_(['llena'])
    assert valor == Q(*cert['valor']), ('valor', valor, cert['valor'])
    resultados.setdefault(v, {})[(a, b)] = valor
    print(f'perfil {v}: {a}f − {b}m ≤ {valor}  ({comprob + 1} columnas comprobadas)')

# cobertura de los 81 perfiles por las órbitas
for v in resultados:
    for g in itertools.permutations(cols):
        img = {tuple(sorted(g[c] for c in U)): v[i] for i, U in enumerate(triples)}
        cubiertos.add(tuple(img[U] for U in triples))
assert cubiertos == todos, 'las órbitas no cubren todos los perfiles'
print(f'cobertura: {len(resultados)} órbitas cubren los {len(todos)} perfiles')
for v, r in sorted(resultados.items()):
    print(' ', v, {f'{a}f-{b}m': (str(x) if x is not None else 'sin cota') for (a, b), x in r.items()})
