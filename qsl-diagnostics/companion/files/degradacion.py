# encaje: socrático nivel 4 (qsl-hardware): ¿los pares cuya puerta de dos cúbits se alargó entre fechas tienen cúbits
# con T1/T2 peores? comparación con los pares no alargados del mismo backend y fechas; investigación.
"""For every backend with two dated snapshots (datos_serie/), every pair present in both: classify as LENGTHENED
(duration up > 5 %), SAME (within 5 %) or SHORTENED. For the two qubits of each pair: change of min(T1) and min(T2)
between dates (log ratio) and change of 2q gate error. Compare groups (Mann-Whitney). Control: if the snapshot's T1
values were copied unchanged between dates, all log ratios would be 0 -- report the fraction of exact zeros."""
import json
from pathlib import Path

import numpy as np
from scipy.stats import mannwhitneyu

D = Path(__file__).parent / 'datos_serie'


def leer(sub):
    p = json.loads(next(sub.glob('props_*.json')).read_text())
    c = json.loads(next(sub.glob('conf_*.json')).read_text())
    if c.get('dt', 0) >= 1:
        return None
    q = {}
    for i, lst in enumerate(p['qubits']):
        v = {x['name']: x['value'] for x in lst}
        if 'T1' in v and 'T2' in v and v['T1'] > 0 and v['T2'] > 0:
            q[i] = (v['T1'], v['T2'])
    pares = {}
    for g in p['gates']:
        if g['gate'] in ('cx', 'ecr', 'cz') and len(g['qubits']) == 2:
            par = {x['name']: x['value'] for x in g['parameters']}
            if 'gate_length' in par:
                k = tuple(sorted(g['qubits']))
                if k not in pares or par['gate_length'] < pares[k][0]:
                    pares[k] = (par['gate_length'], par.get('gate_error'))
    return q, pares


por = {}
for sub in sorted(d for d in D.iterdir() if d.is_dir()):
    nombre, fecha = sub.name.rsplit('_', 1)
    r = leer(sub)
    if r:
        por.setdefault(nombre, []).append((fecha, r))

grupos = {'alargado': [], 'igual': [], 'acortado': []}
ESTR = {}   # (backend, date1, date2) -> group -> [(dT1, dT2)]: stratified control (27-oct: the pooled frequency
#             effect of frecuencia_degradados.py vanished once stratified)
ceros = total = 0
for nombre, lista in por.items():
    lista.sort()
    for (f1, (q1, p1)), (f2, (q2, p2)) in zip(lista, lista[1:]):
        for k in set(p1) & set(p2):
            if not all(i in q1 and i in q2 for i in k):
                continue
            t1, t2 = p1[k][0], p2[k][0]
            if t2 > 3000 or t1 > 3000:
                continue
            dT1 = np.log(min(q2[i][0] for i in k) / min(q1[i][0] for i in k))
            dT2 = np.log(min(q2[i][1] for i in k) / min(q1[i][1] for i in k))
            total += 1
            ceros += dT1 == 0
            g = 'alargado' if t2 > 1.05 * t1 else 'acortado' if t2 < 0.95 * t1 else 'igual'
            grupos[g].append((dT1, dT2))
            ESTR.setdefault((nombre, f1, f2), {}).setdefault(g, []).append((dT1, dT2))
print(f'pares comparables: {total}; con T1 exactamente igual entre fechas: {ceros} ({ceros / max(total, 1):.0%})')
for g, v in grupos.items():
    if v:
        a = np.array(v)
        print(f'  {g:9s} n={len(v):4d}  cambio log T1 mediana {np.median(a[:, 0]):+.3f}   log T2 {np.median(a[:, 1]):+.3f}')
for idx, nom in ((0, 'T1'), (1, 'T2')):
    A = [x[idx] for x in grupos['alargado']]
    B = [x[idx] for x in grupos['igual']]
    if A and B:
        u, p = mannwhitneyu(A, B, alternative='less')
        print(f'  ¿{nom} cae más en los alargados que en los iguales? Mann-Whitney p = {p:.3g}')

from scipy.stats import wilcoxon  # noqa: E402

print('\nCONTROL estratificado (mismo backend y fechas):')
for idx, nom in ((0, 'T1'), (1, 'T2')):
    dif = []
    for gs in ESTR.values():
        if gs.get('alargado') and gs.get('igual'):
            base = np.median([x[idx] for x in gs['igual']])
            dif.extend(x[idx] - base for x in gs['alargado'])
    dif = np.array(dif)
    p = wilcoxon(dif, alternative='less')[1] if len(dif) > 5 else float('nan')
    print(f'  {nom}: alargado − iguales del mismo estrato, mediana {np.median(dif):+.3f} (n = {len(dif)}), '
          f'cae más en {np.mean(dif < 0):.0%}; Wilcoxon p = {p:.3g}')
