# encaje: mediana del cociente de un cúbit con peso por qubit frente a peso por backend, e intervalo por remuestreo
# AGRUPADO por backend (revisión externa 27-oct, punto 2.3); investigación, no herramienta.
"""Reads barrido.csv (one row per qubit). Reports: median over qubits; median of per-backend medians; 95% interval of
the qubit-weighted median by cluster bootstrap (resample backends with replacement, 4000 draws)."""
import csv
from pathlib import Path

import numpy as np

filas = list(csv.DictReader(open(Path(__file__).parent / 'barrido.csv', encoding='utf-8')))
col = next(k for k in filas[0] if 'ratio' in k.lower() or 'cociente' in k.lower() or k.lower().startswith('rx'))
por = {}
for f in filas:
    try:
        por.setdefault(f['backend'], []).append(float(f[col]))
    except ValueError:
        pass
todos = np.concatenate([np.array(v) for v in por.values()])
print(f'columna usada: {col}; backends {len(por)}, qubits {len(todos)}')
print(f'mediana por qubit: {np.median(todos):.2f}')
print(f'mediana de medianas por backend: {np.median([np.median(v) for v in por.values()]):.2f}')
rng = np.random.default_rng(1)
bs = list(por)
meds = [np.median(np.concatenate([por[b] for b in rng.choice(bs, len(bs))])) for _ in range(4000)]
print(f'IC 95 % agrupado por backend: [{np.percentile(meds, 2.5):.2f}, {np.percentile(meds, 97.5):.2f}]')
