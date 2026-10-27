# encaje: prueba «convencion» de ficha_ideas.toml (qsl-hardware): ¿omegad de conf_*.json es la frecuencia de Rabi máxima
# en rad/ns? Simula el Duffing de 3 niveles del propio Hamiltoniano de IBM; investigación, no herramienta.
"""Rotating frame at the qubit frequency, RWA: H = (delta/2) n(n-1) + (Omega/2)(b + b^dag) with Omega = omegad * |D|,
|D| = 1 (square pulse). Time of the first maximum of P(|1>) from |0>. Controls: two-level model gives pi/Omega
exactly; doubling omegad halves the time."""
import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm

DATOS = Path(__file__).parent / 'datos'


def hamiltoniano(omega, delta, niveles):
    b = np.diag(np.sqrt(np.arange(1, niveles)), 1)          # annihilation
    n = b.T @ b
    return delta / 2 * n @ (n - np.eye(niveles)) + omega / 2 * (b + b.T)


def primer_maximo(omega, delta, niveles, tmax=200.0, dt=0.005):
    h = hamiltoniano(omega, delta, niveles)
    u = expm(-1j * h * dt)
    psi = np.zeros(niveles, complex)
    psi[0] = 1
    p_prev, t = 0.0, 0.0
    while t < tmax:
        psi = u @ psi
        t += dt
        p = abs(psi[1]) ** 2
        if p < p_prev:                                       # passed the first maximum
            return t - dt, p_prev
        p_prev = p
    return None, p_prev


h = json.loads((DATOS / 'armonk' / 'conf_armonk.json').read_text())['hamiltonian']['vars']
omegad, delta = h['omegad0'], h['delta0']
print(f'armonk: omegad0 = {omegad:.6f}, delta0 = {delta:.6f} (conf vars), pi/omegad = {np.pi / omegad:.3f} ns')
t2, p2 = primer_maximo(omegad, 0.0, 2)
print(f'control + (2 niveles): t = {t2:.3f} ns, P1 = {p2:.6f}; esperado pi/omegad = {np.pi / omegad:.3f}',
      'OK' if abs(t2 - np.pi / omegad) < 0.02 else 'FALLA')
t2b, _ = primer_maximo(2 * omegad, 0.0, 2)
print(f'control - (omegad x2): t = {t2b:.3f} ns, razón {t2 / t2b:.4f} (esperado 2)',
      'OK' if abs(t2 / t2b - 2) < 0.01 else 'FALLA')
t3, p3 = primer_maximo(omegad, delta, 3)
print(f'Duffing 3 niveles, pulso cuadrado a amplitud 1: t = {t3:.3f} ns, P1 max = {p3:.4f} (fuga a |2> = {1 - p3:.4f})')
props = json.loads((DATOS / 'armonk' / 'props_armonk.json').read_text())
x = [g for g in props['gates'] if g['gate'] == 'x'][0]
tx = [p['value'] for p in x['parameters'] if p['name'] == 'gate_length'][0]
print(f'puerta x de armonk: {tx:.3f} ns; razón tau_x / (pi/omegad) = {tx / (np.pi / omegad):.3f}')
