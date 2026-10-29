# Helper of zl_nauty.py: maximum bases and their automorphisms.
"""python zl_km.py m n [--seg 300] [--max-auts 2000] [--e1-semillas 3]"""
import sys
import time
from collections import Counter

import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
from ortools.sat.python import cp_model

from zl_cpsat import modelo
from zl_cpsat_dlex import modelo_dlex


def e1_extremal(m, n, z_obj=None, semilla=0, seg=120):
    """Una E1 sin C4 de cardinal máximo (CP-SAT con double-lex, semilla distinta para variar)."""
    M, y, _ = modelo(m, n)
    if z_obj is not None:
        M.Add(sum(y.values()) == z_obj)
    else:
        M.Maximize(sum(y.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = seg
    s.parameters.num_workers = 4
    s.parameters.random_seed = semilla
    s.Solve(M)
    return frozenset(c for c, v in y.items() if s.Value(v))


def automorfismos(E1, m, n, maximo):
    G = nx.Graph()
    G.add_nodes_from((('f', i) for i in range(m)), lado='f')
    G.add_nodes_from((('c', j) for j in range(n)), lado='c')
    G.add_edges_from((('f', i), ('c', j)) for i, j in E1)
    gm = GraphMatcher(G, G, node_match=lambda a, b: a['lado'] == b['lado'])
    out = []
    for iso in gm.isomorphisms_iter():
        sig = [iso[('f', i)][1] for i in range(m)]
        tau = [iso[('c', j)][1] for j in range(n)]
        out.append((sig, tau))
        if len(out) >= maximo:
            break
    return out


def orden(sig, tau):
    def ord_perm(p):
        vis, o = set(), 1
        for i in range(len(p)):
            if i in vis:
                continue
            l, j = 0, i
            while j not in vis:
                vis.add(j)
                j = p[j]
                l += 1
            o = o * l // __import__('math').gcd(o, l)
        return o
    a, b = ord_perm(sig), ord_perm(tau)
    return a * b // __import__('math').gcd(a, b)


def max_e2(m, n, E1, seg, g=None):
    M, y, x = modelo(m, n, z=len(E1))
    for c, v in y.items():
        M.Add(v == (1 if c in E1 else 0))
    if g is not None:
        sig, tau = g
        gc = lambda c: (sig[c[0]], tau[c[1]])
        for (a, b), v in x.items():
            M.Add(v == x[tuple(sorted((gc(a), gc(b))))])
    M.Maximize(sum(x.values()))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = seg
    s.parameters.num_workers = 4
    st = s.StatusName(s.Solve(M))
    return st, (int(s.ObjectiveValue()) if st in ('OPTIMAL', 'FEASIBLE') else None), int(s.BestObjectiveBound())


if __name__ == '__main__':
    m, n = int(sys.argv[1]), int(sys.argv[2])
    arg = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
    seg, maxa, semillas = arg('--seg', 300), arg('--max-auts', 2000), arg('--e1-semillas', 3)
    vistos = set()
    for sem in range(semillas):
        E1 = e1_extremal(m, n, semilla=sem)
        if E1 in vistos:
            continue
        vistos.add(E1)
        t0 = time.time()
        auts = automorfismos(E1, m, n, maxa)
        ords = Counter(orden(s, t) for s, t in auts)
        st, e2, cota = max_e2(m, n, E1, seg)
        print(f'E1 #{sem}: |E1| = {len(E1)}, |Aut| ≥ {len(auts)}{"+" if len(auts) >= maxa else ""} '
              f'(órdenes {dict(sorted(ords.items()))}); E1 fija sin simetría: {st} |E2| = {e2} (cota {cota}) '
              f'→ z_L ≥ {len(E1) + (e2 or 0)}  [{time.time() - t0:.0f} s]', flush=True)
        # un representante por orden (el primero encontrado)
        hechos = set()
        for g in auts:
            o = orden(*g)
            if o < 2 or o in hechos:
                continue
            hechos.add(o)
            t1 = time.time()
            st2, e22, _ = max_e2(m, n, E1, min(seg, 120), g)
            print(f'    invariante bajo un automorfismo de orden {o}: {st2} |E2| = {e22} → z_L ≥ '
                  f'{len(E1) + (e22 or 0)}  [{time.time() - t1:.1f} s]', flush=True)
