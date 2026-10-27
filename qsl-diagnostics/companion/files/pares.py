# encaje: extrae los pares acoplados (jq, desintonía) y la duración de su puerta de dos cúbits de las instantáneas de IBM;
# datos para el análisis de dos cúbits de qsl-hardware; investigación, no herramienta.
"""For every backend kept by barrido.py's rule (dt < 1 ns), every pair (i, j) with a coupling jq{i}q{j} in the
Hamiltonian vars and a two-qubit gate (ecr, cx or cz) on (i, j) or (j, i): jq (rad/ns), detuning wq_i - wq_j (rad/ns),
anharmonicities, gate name and duration (ns). Writes pares.csv; prints a summary. The bound itself is NOT computed
here: its constant is being fixed from the literature (LECTURA_DOS_CUBITS.md)."""
import csv
import json
import re
from pathlib import Path

import numpy as np

DATOS = Path(__file__).parent / 'datos'
filas = []
for b in sorted(d.name for d in DATOS.iterdir() if d.is_dir()):
    try:
        c = json.loads((DATOS / b / f'conf_{b}.json').read_text())
        p = json.loads((DATOS / b / f'props_{b}.json').read_text())
    except FileNotFoundError:
        continue
    v = (c.get('hamiltonian') or {}).get('vars', {})
    if not v or c.get('dt', 0) >= 1:
        continue
    dur = {}
    for g in p['gates']:
        if g['gate'] in ('ecr', 'cx', 'cz') and len(g['qubits']) == 2:
            L = [x['value'] for x in g['parameters'] if x['name'] == 'gate_length']
            if L:
                dur.setdefault(tuple(sorted(g['qubits'])), []).append((g['gate'], L[0]))
    for k, J in v.items():
        m = re.fullmatch(r'jq(\d+)q(\d+)', k)
        if not m or not J:
            continue
        i, j = int(m.group(1)), int(m.group(2))
        par = tuple(sorted((i, j)))
        if par not in dur:
            continue
        wi, wj = v.get(f'wq{i}'), v.get(f'wq{j}')
        gate, t = min(dur[par], key=lambda x: x[1])
        filas.append(dict(backend=b, i=par[0], j=par[1], jq=J, det=(wi - wj) if wi and wj else None,
                          di=v.get(f'delta{i}'), dj=v.get(f'delta{j}'), gate=gate, t=t))

with open(Path(__file__).parent / 'pares.csv', 'w', newline='', encoding='utf-8') as f:
    w = csv.DictWriter(f, fieldnames=list(filas[0]))
    w.writeheader()
    w.writerows(filas)
J = np.array([r['jq'] for r in filas])
T = np.array([r['t'] for r in filas])
D = np.array([abs(r['det']) for r in filas if r['det']])
print(f'pares: {len(filas)} en {len({r["backend"] for r in filas})} backends; puertas: '
      f'{ {g: sum(r["gate"] == g for r in filas) for g in ("ecr", "cx", "cz")} }')
print(f'jq (rad/ns): mediana {np.median(J):.5f}  [p5 {np.percentile(J, 5):.5f}, p95 {np.percentile(J, 95):.5f}]  '
      f'= g/2pi mediana {np.median(J) / (2 * np.pi) * 1e3:.2f} MHz')
print(f'|desintonía| (rad/ns): mediana {np.median(D):.3f} = {np.median(D) / (2 * np.pi) * 1e3:.0f} MHz;  '
      f'|desintonía|/jq mediana {np.median(D / np.array([r["jq"] for r in filas if r["det"]])):.1f}')
print(f'duración puerta de dos cúbits (ns): mediana {np.median(T):.0f}  [p5 {np.percentile(T, 5):.0f}, '
      f'p95 {np.percentile(T, 95):.0f}]')
print(f'candidatos a cota (a fijar con la literatura): t*jq/pi mediana {np.median(T * J / np.pi):.2f} '
      f'(= t / (pi/jq));  t/(pi/(2jq)) = {np.median(T * 2 * J / np.pi):.2f};  t/(pi/(4jq)) = {np.median(T * 4 * J / np.pi):.2f}')
