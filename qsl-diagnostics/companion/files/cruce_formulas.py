# encaje: cruce de fórmulas con la calibración real (qsl-hardware): (1) resonancia cruzada: theta_ZX = nu_ZX * t_CR con
# nu_ZX = J*Omega/Delta * delta_c/(Delta + delta_c) frente a pi/2 (CNOT); (2) un cúbit: Omega_pico/|delta|; investigación.
"""Pulse defaults (defs_*.json) from qiskit-terra 0.24.1 (32 backends). For every cx with echoed gaussian_square CR
pulses on a control channel u_k: control qubit c = the qubit whose control channel is u_k, target t = the qubit whose
frequency the channel uses (u_channel_lo). Omega_CR = |amp| * omegad_c; Delta = wq_c - wq_t; delta_c = anharmonicity
of the control; t_CR = sum of areas of the CR pulses (lifted-Gaussian edges + flat top) * dt.
Prediction (Magesan & Gambetta 2020 style, leading order): nu_ZX = -(J Omega/Delta) * delta_c/(delta_c + Delta), and a
CNOT needs a ZX rotation with |nu| t = pi/2 (convention H = (nu/2) ZX). Report theta/(pi/2) per gate.
(2) Single qubit: Omega_peak = |amp_x| * omegad for the calibrated x pulse; ratio Omega_peak/|delta|."""
import json
from pathlib import Path

import numpy as np

RAIZ = (Path(__file__).parent / 'datos_pulsos')   # qiskit-terra 0.24.1 defs/conf (Apache 2.0)


def area_lift(dur, sigma, width=0):
    """Qiskit lifted Gaussian (or GaussianSquare: flat top of `width`), integral in samples with peak 1."""
    t = np.arange(dur) + 0.5
    if width:
        risefall = (dur - width) / 2
        c1, c2 = risefall, risefall + width
        g = np.where(t < c1, np.exp(-((t - c1) ** 2) / (2 * sigma ** 2)),
                     np.where(t > c2, np.exp(-((t - c2) ** 2) / (2 * sigma ** 2)), 1.0))
        g0 = np.exp(-((risefall + 0.5) ** 2) / (2 * sigma ** 2))
    else:
        c = dur / 2
        g = np.exp(-((t - c) ** 2) / (2 * sigma ** 2))
        g0 = np.exp(-((c + 0.5) ** 2) / (2 * sigma ** 2))
    return float(np.sum((g - g0) / (1 - g0)))


def amp_abs(a):
    return abs(complex(*a)) if isinstance(a, list) else abs(a)


tz, r1 = [], []
for b in sorted(RAIZ.iterdir()):
    fd, fc = b / f'defs_{b.name}.json', b / f'conf_{b.name}.json'
    if not (fd.exists() and fc.exists()):
        continue
    d, c = json.loads(fd.read_text()), json.loads(fc.read_text())
    v = (c.get('hamiltonian') or {}).get('vars', {})
    if 'omegad0' not in v:
        continue
    dt = c['dt'] * (1e9 if c['dt'] < 1e-6 else 1)
    ulo = c.get('u_channel_lo', [])
    # control channel u_k belongs to the qubit q whose drive (omegad) is used: Qiskit's channel map gives control
    # qubit; frequency = qubit in u_channel_lo[k]
    chmap = {}
    for q, chs in (c.get('channels') or {}).items():
        pass
    ctrl_of = {}
    for name, info in (c.get('channels') or {}).items():
        if name.startswith('u') and info.get('operates', {}).get('qubits'):
            ctrl_of[int(name[1:])] = info['operates']['qubits'][0]
    for cmd in d.get('cmd_def', []):
        if cmd['name'] == 'x' and len(cmd['qubits']) == 1:
            q = cmd['qubits'][0]
            p = [s for s in cmd['sequence'] if s.get('name') == 'parametric_pulse']
            if p and v.get(f'delta{q}'):
                r1.append(amp_abs(p[0]['parameters']['amp']) * v[f'omegad{q}'] / abs(v[f'delta{q}']))
        if cmd['name'] != 'cx':
            continue
        cr = [s for s in cmd['sequence'] if s.get('ch', '').startswith('u') and s.get('name') == 'parametric_pulse'
              and s.get('pulse_shape') == 'gaussian_square']
        if len(cr) < 2:
            continue
        k = int(cr[0]['ch'][1:])
        if k not in ctrl_of or k >= len(ulo):
            continue
        cq, tq = ctrl_of[k], ulo[k][0]['q']
        J = v.get(f'jq{min(cq, tq)}q{max(cq, tq)}')
        if not J:
            continue
        P = cr[0]['parameters']
        Om = amp_abs(P['amp']) * v[f'omegad{cq}']
        Dl = v[f'wq{cq}'] - v[f'wq{tq}']
        dc = v[f'delta{cq}']
        nu = -(J * Om / Dl) * dc / (dc + Dl)
        t = sum(area_lift(s['parameters']['duration'], s['parameters']['sigma'], s['parameters']['width'])
                for s in cr) * dt
        tz.append(dict(b=b.name, cq=cq, tq=tq, Om=Om, Dl=Dl, ratio=abs(nu) * t / (np.pi / 2), OmDl=abs(Om / Dl)))

tz_r = np.array([x['ratio'] for x in tz])
print(f'(1) CX con resonancia cruzada: {len(tz)} puertas en {len({x["b"] for x in tz})} backends')
print(f'    theta_ZX/(pi/2): mediana {np.median(tz_r):.3f}  [p10 {np.percentile(tz_r, 10):.3f}, p90 '
      f'{np.percentile(tz_r, 90):.3f}]  · |Omega_CR/Delta| mediana {np.median([x["OmDl"] for x in tz]):.3f}')
print(f'    fracción con theta/(pi/2) en [0,8, 1,2]: {np.mean((tz_r > 0.8) & (tz_r < 1.2)):.0%}')
print(f'(2) un cúbit, Omega_pico/|delta|: {len(r1)} cúbits, mediana {np.median(r1):.4f} '
      f'[p10 {np.percentile(r1, 10):.4f}, p90 {np.percentile(r1, 90):.4f}], CV {np.std(r1) / np.mean(r1):.2f}')
