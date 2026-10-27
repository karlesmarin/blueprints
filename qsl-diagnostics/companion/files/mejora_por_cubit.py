# encaje: ¿cuánto se ganaría con duración de la X por cúbit? (qsl-hardware): con la regla medida Omega_pico <= c*|delta|
# (c = p90 observado, 0,099), duración mínima de cada cúbit frente a la común de su backend; investigación.
"""Pulse defaults (qiskit-terra 0.24.1, 32 backends). For each qubit: current peak Rabi Omega_i = |amp_i| omegad_i with
the common duration tau_b. Keeping the same pulse shape, the duration scales as 1/Omega; the largest allowed peak is
c |delta_i| (c = 0.099, the observed 90th percentile — IBM's own cap, not a physics limit). New duration
tau_i = tau_b * Omega_i / (c |delta_i|). Report the per-qubit and per-backend gain (mean single-qubit layer time is
set by the slowest qubit if operations are synchronised: report both the median tau_i/tau_b and the max)."""
import json
from pathlib import Path

import numpy as np

RAIZ = Path(__file__).parent / 'datos_pulsos'   # defs/conf of qiskit-terra 0.24.1 (Apache 2.0), copied 27-oct
C = 0.099
por_q, por_b = [], []
for b in sorted(RAIZ.iterdir()):
    fd, fc = b / f'defs_{b.name}.json', b / f'conf_{b.name}.json'
    if not (fd.exists() and fc.exists()):
        continue
    d, c = json.loads(fd.read_text()), json.loads(fc.read_text())
    v = (c.get('hamiltonian') or {}).get('vars', {})
    dt = c['dt'] * (1e9 if c['dt'] < 1e-6 else 1)
    rel = []
    for cmd in d.get('cmd_def', []):
        if cmd['name'] != 'x' or len(cmd['qubits']) != 1:
            continue
        q = cmd['qubits'][0]
        p = [s for s in cmd['sequence'] if s.get('name') == 'parametric_pulse']
        if not p or not v.get(f'delta{q}') or not v.get(f'omegad{q}'):
            continue
        a = p[0]['parameters']['amp']
        amp = abs(complex(*a)) if isinstance(a, list) else abs(a)
        om = amp * v[f'omegad{q}']
        rel.append(om / (C * abs(v[f'delta{q}'])))          # tau_i / tau_b
        tau_b = p[0]['parameters']['duration'] * dt
    if rel:
        rel = np.array(rel)
        por_q.extend(rel)
        por_b.append((b.name, tau_b, np.median(rel), rel.max()))
por_q = np.array(por_q)
print(f'{len(por_q)} cúbits en {len(por_b)} backends; tau_i/tau_común: mediana {np.median(por_q):.2f}, '
      f'p10 {np.percentile(por_q, 10):.2f}, p90 {np.percentile(por_q, 90):.2f}')
print(f'ganancia mediana por cúbit: x{1 / np.median(por_q):.2f};  si la capa espera al cúbit más lento: '
      f'mediana de max por backend {np.median([x[3] for x in por_b]):.2f} (ganancia x{1 / np.median([x[3] for x in por_b]):.2f})')
for x in por_b[:8]:
    print(f'  {x[0]:12s} tau común {x[1]:5.1f} ns -> mediana {x[1] * x[2]:5.1f} ns, el más lento {x[1] * x[3]:5.1f} ns')
