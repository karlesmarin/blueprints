# Section 7: maximum bases up to isomorphism (nauty) and the largest family for each (CP-SAT).
"""python zl_nauty.py tabla [--mmax 14] [--nmax 9] [--seg 900]      → tabla_zl_nauty.jsonl
   python zl_nauty.py uno m n [--seg 900]

Controles (28-oct): nº de clases 5×5: 2, 6×6: 1, 10×5: 1, 11×4: 6, igual que la enumeración con double-lex + VF2 y,
para 5×5, igual que arXiv:2609.18429 («exactly two isomorphism types»)."""
import json
import subprocess
import sys
import time
from pathlib import Path

import networkx as nx

from zl_km import max_e2

A = Path(__file__).resolve().parent
GENBG = '/home/sage/sage/local/bin/genbg'
ENV = {**__import__('os').environ, 'MSYS_NO_PATHCONV': '1'}


def genbg(m, n, e, contar=False):
    args = ['docker', 'exec', 'cognitive_arch_sage', GENBG, '-Z1', '-q'] + (['-u'] if contar else []) + \
        [str(m), str(n), f'{e}:{e}']
    r = subprocess.run(args, capture_output=True, env=ENV, timeout=7200)
    if contar:
        msg = (r.stderr or b'').decode() + (r.stdout or b'').decode()
        r2 = subprocess.run(args[:4] + ['-u'] + args[5:] if False else
                            ['docker', 'exec', 'cognitive_arch_sage', GENBG, '-Z1', '-u', str(m), str(n), f'{e}:{e}'],
                            capture_output=True, env=ENV, timeout=7200)
        texto = (r2.stderr or b'').decode() + (r2.stdout or b'').decode()
        return int(texto.split('>Z')[1].split('graphs')[0])
    return [l for l in r.stdout.splitlines() if l.strip()]


def z_mn(m, n):
    """Mayor número de aristas de un bipartito m×n sin C4 (busca hacia abajo desde una cota de Reiman)."""
    import math
    a, b = (m, n) if m <= n else (n, m)
    cota = int(min(m * n, (a + math.sqrt(a * a + 4 * a * b * (b - 1))) / 2 + 1))
    for e in range(cota, 0, -1):
        if genbg(m, n, e, contar=True) > 0:
            return e
    return 0


def clases(m, n, z):
    out = []
    for g6 in genbg(m, n, z):
        G = nx.from_graph6_bytes(g6.strip())
        out.append(frozenset((u, v - m) for u, v in ((min(a, b), max(a, b)) for a, b in G.edges()) if u < m <= v))
    return out


def resolver(m, n, seg):
    t0 = time.time()
    z = z_mn(m, n)
    cls = clases(m, n, z)
    mejor, exacto, por = -1, True, []
    from zl_e2_sim import max_e2_sim  # 29-oct: ruptura por filas idénticas de E1 (13×4: 35 min y exacto)
    for E1 in cls:
        assert len(E1) == z, (len(E1), z)
        st, e2, cota = max_e2_sim(m, n, E1, seg)
        exacto = exacto and st == 'OPTIMAL'
        mejor = max(mejor, e2 if e2 is not None else -1)
        por.append([st, e2, cota])
    cota_sup = z + max(c for _, _, c in por) if por else None
    return dict(m=m, n=n, z=z, clases=len(cls), zl=z + mejor, exacto=exacto, cota_sup=cota_sup, por_clase=por,
                s=round(time.time() - t0))


if __name__ == '__main__':
    arg = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
    seg = arg('--seg', 900)
    if sys.argv[1] == 'uno':
        print(resolver(int(sys.argv[2]), int(sys.argv[3]), seg), flush=True)
        sys.exit()
    mmax, nmax = arg('--mmax', 14), arg('--nmax', 9)
    salida = A / 'tabla_zl_nauty.jsonl'
    hechos = {(d['m'], d['n']) for d in map(json.loads, salida.read_text(encoding='utf-8').splitlines())} \
        if salida.exists() else set()
    tam = sorted(((m, n) for m in range(3, mmax + 1) for n in range(3, min(m, nmax) + 1)), key=lambda t: (t[0] * t[1], t))
    for m, n in tam:
        if (m, n) in hechos:
            continue
        f = resolver(m, n, seg)
        with open(salida, 'a', encoding='utf-8') as fh:
            fh.write(json.dumps(f) + '\n')
        print(f"{m}x{n}: z = {f['z']}, clases {f['clases']}, z_L {'=' if f['exacto'] else '≥'} {f['zl']}"
              f"{'' if f['exacto'] else ' (≤ ' + str(f['cota_sup']) + ')'}  [{f['s']} s]", flush=True)
