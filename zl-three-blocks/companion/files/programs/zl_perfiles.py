# Theorem E and Appendix A: the exact profile system (types, ports, permitted pairs), one LP per profile.
"""python zl_perfiles.py n alfa beta [--out dir]"""
import itertools
import json
import sys
from pathlib import Path

n, alfa, beta = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
out = Path(sys.argv[sys.argv.index('--out') + 1]) if '--out' in sys.argv else Path(f'perfiles_n{n}')
out.mkdir(exist_ok=True)
C = tuple(range(n))
TR = [frozenset(t) for t in itertools.combinations(C, 3)]
PARES = [frozenset(p) for p in itertools.combinations(C, 2)]


def emparejamientos(cs):
    """Todos los emparejamientos parciales (conjuntos de pares disjuntos) de la lista cs."""
    cs = sorted(cs)
    if not cs:
        yield ()
        return
    a, resto = cs[0], cs[1:]
    yield from emparejamientos(resto)
    for i, b in enumerate(resto):
        for m in emparejamientos(resto[:i] + resto[i + 1:]):
            yield ((a, b),) + m


def tipos(p):
    """Tipos (B, S, M) compatibles con el perfil p (dict triple -> 0/1/2)."""
    res = []
    bases = [frozenset([a]) for a in C] + PARES
    for B in bases:
        resto = [c for c in C if c not in B]
        for k in range(len(resto) + 1):
            for extra in itertools.combinations(resto, k):
                S = B | frozenset(extra)
                if any(p[U] == 0 for U in TR if U <= S):
                    continue
                for M in emparejamientos(sorted(S - B)):
                    ok = True
                    for (j, q) in M:
                        for l in S - {j, q}:
                            if p[frozenset((j, q, l))] != 1:
                                ok = False
                    if ok:
                        res.append((B, S, M))
    return res


def permitida(S, j, T, q, p):
    if j == q:
        return S & T == {j}
    if q in S and j in T:
        return False
    for l in (S & T) - {j, q}:
        U = frozenset((j, q, l))
        dentro = (U <= S) + (U <= T)
        if p[U] >= 1 + dentro:  # hay una fila externa que contiene U
            return False
    return True


def perfiles_orbitas():
    vistos, reps = set(), []
    for v in itertools.product((0, 1, 2), repeat=len(TR)):
        if v in vistos:
            continue
        orb = set()
        for g in itertools.permutations(C):
            img = [None] * len(TR)
            for i, U in enumerate(TR):
                img[TR.index(frozenset(g[c] for c in U))] = v[i]
            orb.add(tuple(img))
        vistos |= orb
        reps.append(v)
    return reps


reps = perfiles_orbitas()
print(f'n = {n}: {3 ** len(TR)} perfiles, {len(reps)} órbitas', flush=True)
for k, v in enumerate(reps):
    p = dict(zip(TR, v))
    T = tipos(p)
    ports = [(t, j) for t, (B, S, M) in enumerate(T) for j in sorted(S - B) if all(j not in par for par in M)]
    edges = [(a, b) for a, b in itertools.combinations(range(len(ports)), 2)
             if ports[a][0] != ports[b][0] and permitida(T[ports[a][0]][1], ports[a][1], T[ports[b][0]][1], ports[b][1], p)]
    # variables: N_t (tipos), y_e (aristas), m
    nv = len(T) + len(edges) + 1
    im = nv - 1
    eq, ge, le = [], [], []  # filas (dict col -> coef, rhs)
    eqk, gek, lek = [], [], []  # claves semánticas de cada restricción (para el comprobador independiente)

    def tk(t):
        B, S, M = T[t]
        return [sorted(B), sorted(S), sorted(sorted(x) for x in M)]
    for P2 in PARES:
        eq.append(({t: 1 for t, (B, S, M) in enumerate(T) if B == P2}, 1))
        eqk.append(['par', sorted(P2)])
    row = {t: 1 for t, (B, S, M) in enumerate(T) if len(B) == 1}
    row[im] = -1
    eq.append((row, -len(PARES)))
    eqk.append(['singleton'])
    for pi, (t, j) in enumerate(ports):
        row = {len(T) + e: 1 for e, (a, b) in enumerate(edges) if pi in (a, b)}
        row[t] = row.get(t, 0) - 1
        eq.append((row, 0))
        eqk.append(['puerto', tk(t), j])
    for U in TR:
        row = {t: 1 for t, (B, S, M) in enumerate(T) if U <= S}
        if p[U] == 0:
            eq.append((row, 0))
            eqk.append(['triple', sorted(U)])
        elif p[U] == 1:
            eq.append((row, 1))
            eqk.append(['triple', sorted(U)])
        else:
            ge.append((row, 2))
            gek.append(['triple', sorted(U)])
    le.append(({t: 1 for t, (B, S, M) in enumerate(T) if len(S) == n}, 1))  # a lo sumo una fila llena (Lema 5.2, formalizado)
    lek.append(['llena'])
    c = {t: alfa * len(M) for t, (B, S, M) in enumerate(T) if M}
    for e in range(len(edges)):
        c[len(T) + e] = alfa
    c[im] = -beta
    json.dump({'perfil': list(v), 'alfa': alfa, 'beta': beta, 'eq_keys': eqk, 'ge_keys': gek, 'le_keys': lek,
               'nv': nv, 'c': {str(a): b for a, b in c.items()},
               'eq': [[{str(a): b for a, b in r.items()}, h] for r, h in eq],
               'ge': [[{str(a): b for a, b in r.items()}, h] for r, h in ge],
               'le': [[{str(a): b for a, b in r.items()}, h] for r, h in le]},
              open(out / f'lp_{alfa}_{beta}_{k:02d}.json', 'w'))
    print(f'  órbita {k}: perfil {v}, {len(T)} tipos, {len(ports)} puertos, {len(edges)} aristas', flush=True)
