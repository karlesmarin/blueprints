# encaje: socrático sobre serie.csv: ¿por qué empeora el cociente de dos cúbits? separa por familia (nº de cúbits),
# puerta (cx/ecr), acoplo jq y duración; investigación, no herramienta.
"""Families by qubit count (5/7 Canary-Falcon small, 16/27 Falcon, 33 Hummingbird-r?, 65 Hummingbird, 127 Eagle).
For each useful snapshot: gate type, median jq, median 2q duration, median ratio. If the ratio grows because jq falls
at fixed duration, or because duration grows at fixed jq, the decomposition says which."""
import json
import re
from pathlib import Path

import numpy as np

D = Path(__file__).parent / 'datos_serie'
filas = []
for sub in sorted(d for d in D.iterdir() if d.is_dir()):
    props = next(sub.glob('props_*.json'))
    conf = next(sub.glob('conf_*.json'))
    c, p = json.loads(conf.read_text()), json.loads(props.read_text())
    v = (c.get('hamiltonian') or {}).get('vars', {})
    if not v or c.get('dt', 0) >= 1:
        continue
    t2, tipo = {}, {}
    for g in p['gates']:
        L = [x['value'] for x in g['parameters'] if x['name'] == 'gate_length']
        if L and g['gate'] in ('cx', 'ecr', 'cz') and len(g['qubits']) == 2:
            k = tuple(sorted(g['qubits']))
            if L[0] < t2.get(k, 1e9):
                t2[k], tipo[k] = L[0], g['gate']
    js, ts, rs, gs = [], [], [], []
    for k, val in v.items():
        m = re.fullmatch(r'jq(\d+)q(\d+)', k)
        if m and val:
            par = tuple(sorted((int(m.group(1)), int(m.group(2)))))
            if par in t2:
                js.append(val)
                ts.append(t2[par])
                rs.append(t2[par] / (np.pi / (2 * val)))
                gs.append(tipo[par])
    if rs:
        filas.append((sub.name.rsplit('_', 1)[1], sub.name.rsplit('_', 1)[0], c.get('n_qubits'),
                      max(set(gs), key=gs.count), np.median(js) / (2 * np.pi) * 1e3, np.median(ts), np.median(rs)))

print(f'{"fecha":10s} {"backend":12s} {"n":>4s} {"puerta":6s} {"g/2pi MHz":>9s} {"t2q ns":>7s} {"2q/QSL":>7s}')
for f in sorted(filas):
    print(f'{f[0]:10s} {f[1]:12s} {f[2]:4d} {f[3]:6s} {f[4]:9.2f} {f[5]:7.0f} {f[6]:7.2f}')
print('\nPor familia (nº de cúbits) y puerta:')
grupos = {}
for f in filas:
    grupos.setdefault((f[2], f[3]), []).append(f)
for (n, g), fs in sorted(grupos.items()):
    print(f'  {n:4d} cúbits · {g:4s}: {len(fs):2d} inst. · g/2π {np.median([x[4] for x in fs]):.2f} MHz · '
          f't2q {np.median([x[5] for x in fs]):.0f} ns · cociente {np.median([x[6] for x in fs]):.2f}')
# same backend over time
print('\nMismo procesador en fechas distintas:')
porb = {}
for f in filas:
    porb.setdefault(f[1], []).append(f)
for b, fs in sorted(porb.items()):
    if len(fs) > 1:
        print('  ' + b + ': ' + ' → '.join(f'{x[0]} ({x[3]}, {x[4]:.2f} MHz, {x[5]:.0f} ns, {x[6]:.2f})'
                                           for x in sorted(fs)))
