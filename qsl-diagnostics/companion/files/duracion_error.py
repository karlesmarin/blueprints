# encaje: socrático, nivel 3: ¿IBM alarga las puertas de dos cúbits para bajar el error? duración frente a gate_error
# entre instantáneas y dentro del mismo par a lo largo del tiempo (datos_serie/); investigación, no herramienta.
"""(a) Across snapshots: Spearman correlation of median 2q duration vs median 2q gate_error (toronto 2021, median
6315 ns, excluded as degraded). (b) Same backend, same pair, two dates: when the duration grows, does the error fall?
(c) Control: 1q gates (fixed duration within a backend) should show no duration-error relation inside a backend."""
import json
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

D = Path(__file__).parent / 'datos_serie'
inst = {}
for sub in sorted(d for d in D.iterdir() if d.is_dir()):
    p = json.loads(next(sub.glob('props_*.json')).read_text())
    c = json.loads(next(sub.glob('conf_*.json')).read_text())
    if c.get('dt', 0) >= 1:
        continue
    pares = {}
    for g in p['gates']:
        if g['gate'] in ('cx', 'ecr', 'cz') and len(g['qubits']) == 2:
            par = {x['name']: x['value'] for x in g['parameters']}
            if 'gate_length' in par and 'gate_error' in par and par['gate_error'] < 1:
                k = tuple(sorted(g['qubits']))
                if k not in pares or par['gate_length'] < pares[k][0]:
                    pares[k] = (par['gate_length'], par['gate_error'])
    if pares:
        nombre, fecha = sub.name.rsplit('_', 1)
        inst[(nombre, fecha)] = pares

filas = [(k, np.median([v[0] for v in ps.values()]), np.median([v[1] for v in ps.values()])) for k, ps in inst.items()]
filas = [f for f in filas if f[1] < 3000]       # toronto 2021 (6315 ns) excluded: degraded
r, pv = spearmanr([f[1] for f in filas], [f[2] for f in filas])
print(f'(a) {len(filas)} instantáneas: Spearman(duración, error) = {r:+.3f} (p = {pv:.3g})')

subidas, bajadas = [], []
porb = {}
for (b, f), ps in inst.items():
    porb.setdefault(b, []).append((f, ps))
for b, lista in porb.items():
    lista.sort()
    for (f1, p1), (f2, p2) in zip(lista, lista[1:]):
        for k in set(p1) & set(p2):
            (t1, e1), (t2, e2) = p1[k], p2[k]
            if t2 > t1 * 1.05 and t2 < 3000:
                subidas.append(np.log(e2 / e1))
            elif t2 < t1 * 0.95:
                bajadas.append(np.log(e2 / e1))
print(f'(b) mismo par en dos fechas: alargadas {len(subidas)} (log error2/error1 mediana {np.median(subidas):+.3f}, '
      f'error baja en {np.mean(np.array(subidas) < 0):.0%}); acortadas {len(bajadas)}'
      + (f' (mediana {np.median(bajadas):+.3f})' if bajadas else ''))
