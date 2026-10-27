# encaje: tiempo mínimo para crear un estado de Bell (máx. coeficiente de Schmidt <= 1/sqrt2) desde un producto, con
# acoplo fijo entre dos cúbits, control local ilimitado y ancillas locales opcionales (qsl-hardware); investigación.
"""Each side = qubit (x) ancilla of dimension da (local dimension D = 2 da). Hc acts on the two main qubits:
  heis: XX + YY + ZZ (norm 3)   ising: ZZ (norm 1)   xy: (XX + YY)/2 (norm 1).
psi(T) = prod_k exp(-i tau (A_k x I + I x B_k + Hc)) |0...0>, A_k, B_k Hermitian D x D (unbounded; the first step
also prepares any product state). Objective: largest Schmidt coefficient across A|B of psi(T). For each T, minimise
it; T* is where it first reaches 1/sqrt2.
References: Dür et al. 2001 (no ancilla): heis T* = pi/(4*2) = 0.3927, ising pi/4 = 0.7854, xy pi/4 (h = 1/2+1/2).
Our bound: T* >= arccos(1/sqrt2)/||Hc|| = (pi/4)/||Hc||: heis 0.2618, ising 0.7854, xy 0.7854."""
import sys

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(5)
tipo, da, M = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
Ts = [float(x) for x in sys.argv[4].split(',')]
X = np.array([[0, 1], [1, 0]], complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1.0, -1.0]).astype(complex)
pares = {'heis': [(X, X), (Y, Y), (Z, Z)], 'ising': [(Z, Z)], 'xy': [(X / np.sqrt(2), X / np.sqrt(2)),
                                                                     (Y / np.sqrt(2), Y / np.sqrt(2))]}[tipo]
Ia = np.eye(da)
D = 2 * da
Hc = sum(np.kron(np.kron(P, Ia), np.kron(Q, Ia)) for P, Q in pares)
nH = np.linalg.norm(Hc, 2)
ID = np.eye(D)
psi0 = np.zeros(D * D, complex)
psi0[0] = 1


def herm(x):
    A = np.zeros((D, D), complex)
    iu = np.triu_indices(D, 1)
    k = D * (D - 1) // 2
    A[iu] = x[:k] + 1j * x[k:2 * k]
    A = A + A.conj().T
    A[np.diag_indices(D)] = x[2 * k:2 * k + D]
    return A


n = D * D


def lam_max(x, T):
    tau = T / M
    psi = np.kron(expm(1j * herm(x[0:n])), expm(1j * herm(x[n:2 * n]))) @ psi0   # free initial product state
    q = 2 * n
    for _ in range(M):
        L = np.kron(herm(x[q:q + n]), ID) + np.kron(ID, herm(x[q + n:q + 2 * n]))
        q += 2 * n
        psi = expm(-1j * tau * (L + Hc)) @ psi
    s = np.linalg.svd(psi.reshape(D, D), compute_uv=False)
    return s[0]


npar = 2 * n + M * 2 * n
obj = 1 / np.sqrt(2)
print(f'{tipo}, ancilla dim {da} (local D = {D}), M = {M}, ||Hc|| = {nH:.3f}, cota (pi/4)/||Hc|| = '
      f'{np.pi / 4 / nH:.4f}, parámetros {npar}', flush=True)
for T in Ts:
    mejor = 1.0
    for s in range(8):
        r = minimize(lam_max, rng.normal(size=npar) * 0.8, args=(T,), method='L-BFGS-B',
                     options=dict(maxiter=4000, maxfun=500000))
        mejor = min(mejor, r.fun)
        if mejor <= obj + 1e-7:
            break
    print(f'  T = {T:.4f}  ->  max Schmidt = {mejor:.6f}  ({"BELL ALCANZADO" if mejor <= obj + 1e-6 else "no"})',
          flush=True)
