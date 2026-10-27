# encaje: socrático nivel 5 (qsl-hardware): ¿cambió la frecuencia de los cúbits de los pares alargados entre fechas?
# y ¿cambió la desintonía del par? (hipótesis TLS / colisión de frecuencias); investigación, no herramienta.
"""Same pairing as degradacion.py. For each comparable pair: |Delta f| of each qubit between dates (props 'frequency',
GHz, measured), change of the pair detuning |f_c - f_t| and of the anharmonicity. Groups: lengthened / same /
shortened. Control: if frequencies were copied unchanged, |Delta f| = 0 exactly; report the fraction of zeros."""
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
        if v.get('frequency'):
            q[i] = (v['frequency'], v.get('anharmonicity'))
    pares = {}
    for g in p['gates']:
        if g['gate'] in ('cx', 'ecr', 'cz') and len(g['qubits']) == 2:
            par = {x['name']: x['value'] for x in g['parameters']}
            if 'gate_length' in par:
                k = tuple(sorted(g['qubits']))
                pares[k] = min(pares.get(k, 1e9), par['gate_length'])
    return q, pares


por = {}
for sub in sorted(D.iterdir()):
    nombre, fecha = sub.name.rsplit('_', 1)
    r = leer(sub)
    if r:
        por.setdefault(nombre, []).append((fecha, r))
G = {'alargado': [], 'igual': [], 'acortado': []}
ESTR = {}   # (backend, date1, date2) -> group -> [df]: the stratified control
ceros = tot = 0
for nombre, lista in por.items():
    lista.sort()
    for (f1, (q1, p1)), (f2, (q2, p2)) in zip(lista, lista[1:]):
        for k in set(p1) & set(p2):
            if not all(i in q1 and i in q2 for i in k) or max(p1[k], p2[k]) > 3000:
                continue
            df = max(abs(q2[i][0] - q1[i][0]) for i in k) * 1e3                  # MHz, worst qubit
            ddet = (abs(q2[k[0]][0] - q2[k[1]][0]) - abs(q1[k[0]][0] - q1[k[1]][0])) * 1e3
            tot += 1
            ceros += df == 0
            g = 'alargado' if p2[k] > 1.05 * p1[k] else 'acortado' if p2[k] < 0.95 * p1[k] else 'igual'
            G[g].append((df, ddet))
            ESTR.setdefault((nombre, f1, f2), {}).setdefault(g, []).append(df)
print(f'pares comparables: {tot}; con frecuencia idéntica entre fechas: {ceros} ({ceros / max(tot, 1):.0%})')
for g, v in G.items():
    if v:
        a = np.array(v)
        print(f'  {g:9s} n={len(v):4d}  |cambio de frecuencia| (peor cúbit) mediana {np.median(a[:, 0]):6.2f} MHz · '
              f'cambio de desintonía mediana {np.median(a[:, 1]):+6.2f} MHz · |desintonía| baja en {np.mean(a[:, 1] < 0):.0%}')
A, B = [x[0] for x in G['alargado']], [x[0] for x in G['igual']]
print(f'¿la frecuencia cambia más en los alargados? Mann-Whitney p = {mannwhitneyu(A, B, alternative="greater")[1]:.3g}')
A, B = [x[1] for x in G['alargado']], [x[1] for x in G['igual']]
print(f'¿la desintonía baja más en los alargados?   Mann-Whitney p = {mannwhitneyu(A, B, alternative="less")[1]:.3g}')

# stratified control: only (backend, date1, date2) strata with both lengthened and unchanged pairs; within each
# stratum, compare the lengthened pairs with the unchanged ones of the SAME backend and dates
dentro, n_est = [], 0
for clave, gs in ESTR.items():
    if gs.get('alargado') and gs.get('igual'):
        n_est += 1
        base = np.median(gs['igual'])
        dentro.extend(np.log((np.array(gs['alargado']) + 1e-3) / (base + 1e-3)))
dentro = np.array(dentro)
print(f'\nCONTROL estratificado ({n_est} estratos backend+fechas, {len(dentro)} pares alargados):')
print(f'  log(|Δf| alargado / mediana |Δf| de los iguales del mismo estrato): mediana {np.median(dentro):+.2f} '
      f'(= x{np.exp(np.median(dentro)):.1f}); mayor que los iguales en {np.mean(dentro > 0):.0%} de los pares')
conc = {}
for clave, gs in ESTR.items():
    if gs.get('alargado'):
        conc[clave[0]] = conc.get(clave[0], 0) + len(gs['alargado'])
print(f'  concentración: los alargados vienen de {len(conc)} backends; los 3 primeros reúnen '
      f'{sum(sorted(conc.values())[-3:]) / sum(conc.values()):.0%}: {sorted(conc.items(), key=lambda x: -x[1])[:5]}')
