# encaje: fija la convención de omegad con un dato independiente: el pulso x CALIBRADO por IBM (defs_*.json de
# qiskit-terra 0.24.1) debe tener área de Rabi pi; investigación, no herramienta.
"""For each backend with pulse defaults, take the calibrated x pulse on qubit 0 (Drag: amp, sigma, duration, beta),
compute A = integral of |envelope| dt (dt from conf) and the rotation angle omegad * |amp| * A * c for the two
candidate conventions c = 1 (Omega = omegad |D|, used in convencion.py) and c = 2. The calibrated x is a pi rotation,
so the right convention gives pi (up to the DRAG correction and the lifted-Gaussian detail)."""
import json
import sys
from pathlib import Path

import numpy as np

RAIZ = Path(sys.argv[1]) if len(sys.argv) > 1 else (Path(__file__).parent / 'datos_pulsos')   # qiskit-terra 0.24.1 defs/conf (Apache 2.0)


def area_gauss(duration, sigma):
    """Lifted Gaussian of Qiskit (zero at the ends, peak 1), integral in samples."""
    t = np.arange(duration) + 0.5
    c = duration / 2
    g = np.exp(-((t - c) ** 2) / (2 * sigma ** 2))
    g0 = np.exp(-((-1 - c + 0.5 + 0.5) ** 2) / (2 * sigma ** 2))   # value one sample outside, as in Qiskit
    return float(np.sum((g - g0) / (1 - g0)))


filas = []
for b in sorted(RAIZ.iterdir()):
    defs = b / f'defs_{b.name}.json'
    conf = b / f'conf_{b.name}.json'
    if not (defs.exists() and conf.exists()):
        continue
    d, c = json.loads(defs.read_text()), json.loads(conf.read_text())
    ham = (c.get('hamiltonian') or {}).get('vars', {})
    if 'omegad0' not in ham:
        continue
    x = [cmd for cmd in d.get('cmd_def', []) if cmd['name'] == 'x' and cmd['qubits'] == [0]]
    if not x:
        continue
    pulsos = [s for s in x[0]['sequence'] if s.get('name') == 'parametric_pulse']
    if not pulsos:
        continue
    p = pulsos[0]['parameters']
    amp = abs(complex(*p['amp'])) if isinstance(p['amp'], list) else abs(p['amp'])
    dt_ns = c['dt'] * 1e9 if c['dt'] < 1e-6 else c['dt']                    # these confs give dt in ns already
    area = area_gauss(p['duration'], p['sigma']) * dt_ns                      # ns
    th1 = ham['omegad0'] * amp * area
    filas.append((b.name, pulsos[0]['pulse_shape'], p['duration'], p['sigma'], amp, ham['omegad0'], th1, 2 * th1))

print(f'{"backend":12s} {"forma":6s} {"dur":>5s} {"sigma":>6s} {"amp":>7s} {"omegad":>8s} {"theta(c=1)/pi":>14s} '
      f'{"theta(c=2)/pi":>14s}')
for f in filas:
    print(f'{f[0]:12s} {f[1]:6s} {f[2]:5d} {f[3]:6.1f} {f[4]:7.4f} {f[5]:8.5f} {f[6] / np.pi:14.3f} {f[7] / np.pi:14.3f}')
if filas:
    r1 = np.array([f[6] / np.pi for f in filas])
    print(f'n = {len(filas)}; mediana theta/pi: c=1 -> {np.median(r1):.3f}, c=2 -> {2 * np.median(r1):.3f}')
