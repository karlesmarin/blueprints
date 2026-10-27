# encaje: verificación INDEPENDIENTE (numpy/scipy, sin torch) de las soluciones CZ guardadas por grape_cz_torch.py:
# 1-F, fuga, fases del bloque y picos de control; investigación, no herramienta.
"""Rebuilds U from the saved parameter vector with the same parametrisation (Hermitian generators from real vectors;
local pre/post unitaries; M piecewise-constant segments; exchange Hc = b1^dag b2 + h.c.) using scipy.linalg.expm.
Usage: python verificar_cz.py cz_best_d3_M8_T0.6000_aNone.npy [...]"""
import re
import sys

import numpy as np
from scipy.linalg import expm


def herm(x, d):
    k = d * (d - 1) // 2
    A = np.zeros((d, d), complex)
    iu = np.triu_indices(d, 1)
    A[iu] = x[:k] + 1j * x[k:2 * k]
    A = A + A.conj().T
    A[np.diag_indices(d)] = x[2 * k:2 * k + d]
    return A


def acotar(A, amax):
    if amax is None:
        return A
    s = np.linalg.norm(A, 2) + 1e-12
    return A * (amax * np.tanh(s / amax) / s)


for f in (sys.argv[1:] if __name__ == '__main__' else []):
    m = re.search(r'd(\d+)_M(\d+)_T([\d.]+)_a([\w.]+)\.npy', f)
    d, M, T = int(m[1]), int(m[2]), float(m[3])
    amax = None if m[4] == 'None' else float(m[4])
    x = np.load(f)
    n = d * d
    b = np.diag(np.sqrt(np.arange(1, d)), 1)
    Hc = np.kron(b.T, b) + np.kron(b, b.T)
    U = np.kron(expm(1j * herm(x[0:n], d)), expm(1j * herm(x[n:2 * n], d)))
    q, picos = 4 * n, 0.0
    for _ in range(M):
        A, B = acotar(herm(x[q:q + n], d), amax), acotar(herm(x[q + n:q + 2 * n], d), amax)
        picos = max(picos, np.linalg.norm(A, 2), np.linalg.norm(B, 2))
        U = expm(-1j * (T / M) * (np.kron(A, np.eye(d)) + np.kron(np.eye(d), B) + Hc)) @ U
        q += 2 * n
    U = np.kron(expm(1j * herm(x[2 * n:3 * n], d)), expm(1j * herm(x[3 * n:4 * n], d))) @ U
    idx = [i * d + j for i in range(2) for j in range(2)]
    Bq = U[np.ix_(idx, idx)]
    infid = 1 - abs(np.trace(np.diag([1, 1, 1, -1]) @ Bq)) / 4
    fuga = 1 - np.linalg.norm(Bq, 'fro') ** 2 / 4
    fase = np.angle(np.diag(Bq) / Bq[0, 0]) / np.pi
    print(f'{f}: T = {T} ({T / (np.pi / 2):.3f} x pi/2), 1-F = {infid:.2e}, fuga = {fuga:.1e}, '
          f'fases/pi = {np.round(fase, 4)}, max ||A_k|| = {picos:.1f} J')
