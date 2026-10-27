# encaje: ¿usa la CZ rápida el nivel |2>? Población máxima fuera del subespacio de cúbits a lo largo de una solución
# guardada por grape_cz_torch.py (comprueba una afirmación del paper, sec. VII); investigación, no herramienta.
"""For each computational input |ij> (i,j in {0,1}) evolve segment by segment (with the local pre-unitary first) and
record the population outside the qubit subspace after every segment (and at 20 sub-steps per segment).
Usage: python poblacion_cz.py cz_best_d3_M8_T0.5500_a10.0.npy"""
import re
import sys

import numpy as np
from scipy.linalg import expm

from verificar_cz import acotar, herm

f = sys.argv[1]
m = re.search(r'd(\d+)_M(\d+)_T([\d.]+)_a([\w.]+)\.npy', f)
d, M, T = int(m[1]), int(m[2]), float(m[3])
amax = None if m[4] == 'None' else float(m[4])
x = np.load(f)
n = d * d
b = np.diag(np.sqrt(np.arange(1, d)), 1)
Hc = np.kron(b.T, b) + np.kron(b, b.T)
idx = [i * d + j for i in range(2) for j in range(2)]
fuera = [k for k in range(n * 1) if k not in idx]
U = np.kron(expm(1j * herm(x[0:n], d)), expm(1j * herm(x[n:2 * n], d)))
q, sub = 4 * n, 20
peor = 0.0
for _ in range(M):
    A, B = acotar(herm(x[q:q + n], d), amax), acotar(herm(x[q + n:q + 2 * n], d), amax)
    paso = expm(-1j * (T / M / sub) * (np.kron(A, np.eye(d)) + np.kron(np.eye(d), B) + Hc))
    for _ in range(sub):
        U = paso @ U
        pob = (np.abs(U[np.ix_(fuera, idx)]) ** 2).sum(axis=0)
        peor = max(peor, pob.max())
    q += 2 * n
print(f'{f}: población máxima fuera del subespacio de cúbits durante la puerta = {peor:.3f}')
