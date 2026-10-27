# encaje: comprobaciones PROPIAS de la tercera revisión externa (27-oct): (1) preparación de Bell exacta por |12>-|21>;
# (2) cota de puerta por el estado de Choi, T >= (pi/4 - arccos(1-e))/(2J); (3) cota del X en la métrica de traza,
# T >= 2 arcsin(1-e)/Omega; (4) r_full = omegad/|delta| de los dispositivos. Investigación, no herramienta.
import csv
from pathlib import Path

import numpy as np
from scipy.linalg import expm

# (1) |12> <-> |21> under exchange, d = 3, J = 1
d = 3
a = np.diag(np.sqrt(np.arange(1, d)), 1)
Hc = np.kron(a.T, a) + np.kron(a, a.T)
k12, k21 = 1 * d + 2, 2 * d + 1
print('(1) <21|Hc|12> =', Hc[k21, k12], '; Hc|12> stays in span{12,21}:',
      np.allclose(np.delete(Hc[:, k12], [k12, k21]), 0))
eps = 5.2e-8
T = (np.pi / 4 - np.arcsin(np.sqrt(eps))) / 2
v = expm(-1j * T * Hc)[:, k12]
c, s = abs(v[k12]), abs(v[k21])
print(f'    T = {T:.12f}: amplitudes cos {c:.9f}, sin {s:.9f}; Bell infidelity 1 - cos^2(pi/4 - 2T) = '
      f'{1 - np.cos(np.pi / 4 - 2 * T) ** 2:.6e}')
# (2) Choi bound
e = 2e-8
print(f'(2) Choi: T_CZ(e={e}) >= (pi/4 - arccos(1-e))/2 = {(np.pi / 4 - np.arccos(1 - e)) / 2:.12f} /J')
# check the Choi identity |<Omega_V|Omega_U>| = |Tr(V^dag P U P)|/4 on a random sub-unitary block
rng = np.random.default_rng(0)
G = rng.normal(size=(9, 9)) + 1j * rng.normal(size=(9, 9))
U = np.linalg.qr(G)[0]
idx = [0, 1, 3, 4]
B = U[np.ix_(idx, idx)]
CZ = np.diag([1, 1, 1, -1]).astype(complex)
# Choi vectors on (A B) x (A' B'): sum_{ij} (M|ij>) |ij>/2, M = 4x? embed: U acts on 9-dim, input in code
psiU = np.zeros((9, 4), complex)
for col, k in enumerate(idx):
    psiU[:, col] = U[:, k]
psiV = np.zeros((9, 4), complex)
for col, k in enumerate(idx):
    psiV[k, col] = CZ[col, col]
ov = abs(np.vdot(psiV.ravel(), psiU.ravel())) / 4
print('    Choi overlap identity:', np.isclose(ov, abs(np.trace(CZ.conj().T @ B)) / 4))
# (3) X bound in the trace metric
for r, Tf in ((0.1, 33.0), (0.2, 16.5)):
    lb = 2 * np.arcsin(1 - 1e-4) / r
    print(f'(3) r = {r}: bound {lb:.6f}/|delta|, found {Tf}, ratio {Tf / lb:.6f}')
d207 = 2.07
print(f'    IBM cap r=0.1, |delta|=2.07: bound {2 * np.arcsin(1 - 1e-4) / 0.1 / d207:.3f} ns, found {33.0 / d207:.3f} ns;'
      f' 35.6 ns is {35.6 / (33.0 / d207):.2f}-{35.6 / (2 * np.arcsin(1 - 1e-4) / 0.1 / d207):.2f} x the minimum')
print(f'    falsifier threshold R_X >= (2/pi) arcsin(1-1e-4) = {2 / np.pi * np.arcsin(1 - 1e-4):.6f}')
# (4) r_full
filas = list(csv.DictReader(open(Path(__file__).parent / 'barrido.csv', encoding='utf-8')))
rf = np.array([float(f['omegad']) / abs(float(f['delta'])) for f in filas])
print(f'(4) r_full = omegad/|delta| over {len(rf)} qubits: median {np.median(rf):.3f}, 5-95% '
      f'[{np.percentile(rf, 5):.3f}, {np.percentile(rf, 95):.3f}], max {rf.max():.3f}')
