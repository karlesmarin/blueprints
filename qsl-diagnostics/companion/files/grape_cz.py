# encaje: control óptimo (GRAPE con gradiente numérico) del tiempo mínimo de una CZ con niveles extra bajo acoplo de
# intercambio J (b1^dag b2 + h.c.) y control local ilimitado (qsl-hardware); investigación, no herramienta.
"""U = Upost * prod_k exp(-i tau (A_k x I + I x B_k + Hc)) * Upre, local A_k, B_k Hermitian d x d (unbounded),
Upre/Upost local d-level unitaries. Fidelity F = |Tr(CZ^dag P U P)| / 4 (P = qubit subspace) is 1 iff the qubit block
is CZ up to a phase with no leakage. For each total time T (units 1/J) maximise F from several random starts.
Control: d = 2 must need T ~ pi/2 (Howard App. C: pi/(4g) with g = J/2 for the XY coupling).
Bound (certified argument, this project): T >= pi/(4 ||Hc||); ||Hc|| = 1 (d = 2), 2 (d = 3)."""
import sys

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(3)
d = int(sys.argv[1]) if len(sys.argv) > 1 else 2
M = int(sys.argv[2]) if len(sys.argv) > 2 else 10
Ts = [float(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [1.2, 1.4, 1.5, 1.571, 1.65]
b = np.diag(np.sqrt(np.arange(1, d)), 1)
I = np.eye(d)
Hc = np.kron(b.T, b) + np.kron(b, b.T)
nH = np.linalg.norm(Hc, 2)
CZ = np.diag([1, 1, 1, -1]).astype(complex)
idx = [i * d + j for i in range(2) for j in range(2)]
n = d * d


def herm(x):
    A = np.zeros((d, d), complex)
    iu = np.triu_indices(d, 1)
    k = d * (d - 1) // 2
    A[iu] = x[:k] + 1j * x[k:2 * k]
    A = A + A.conj().T
    A[np.diag_indices(d)] = x[2 * k:2 * k + d]
    return A


def U_of(x, T):
    tau = T / M
    p = 0
    loc = lambda: (expm(1j * herm(x[p:p + n])))
    Upre = np.kron(expm(1j * herm(x[0:n])), expm(1j * herm(x[n:2 * n])))
    Upost = np.kron(expm(1j * herm(x[2 * n:3 * n])), expm(1j * herm(x[3 * n:4 * n])))
    U = Upre
    q = 4 * n
    for _ in range(M):
        L = np.kron(herm(x[q:q + n]), I) + np.kron(I, herm(x[q + n:q + 2 * n]))
        q += 2 * n
        U = expm(-1j * tau * (L + Hc)) @ U
    return Upost @ U


def infid(x, T):
    U = U_of(x, T)
    B = U[np.ix_(idx, idx)]
    return 1 - abs(np.trace(CZ.conj().T @ B)) / 4


npar = 4 * n + M * 2 * n
print(f'd={d}, M={M}, ||Hc|| = {nH:.4f}, cota pi/(4||Hc||) = {np.pi / (4 * nH):.4f}, parámetros {npar}', flush=True)
for T in Ts:
    mejor = 1.0
    for s in range(6):
        r = minimize(infid, rng.normal(size=npar) * 0.8, args=(T,), method='L-BFGS-B',
                     options=dict(maxiter=3000, maxfun=400000))
        mejor = min(mejor, r.fun)
        if mejor < 1e-8:
            break
    print(f'  T = {T:.3f}/J  ->  1 - F = {mejor:.2e}', flush=True)
