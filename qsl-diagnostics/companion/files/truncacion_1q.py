# encaje: ¿depende el pulso X rápido de grape_1q.py del corte a L niveles? Optimiza con L = 4 en r = 1.0 cerca del
# tiempo hallado (6.9/|delta|), guarda el pulso y lo repropaga SIN CAMBIOS con L = 5, 6, 8, 12; calcula además el
# certificado de Duhamel eta = int |u| ||<L-1|U P_comp|| dt (cota de la distancia al modelo mayor). Investigación.
"""Same model and parametrization as grape_1q.py (delta = -1, units |delta| = 1, drive amp r tanh(x) e^{i phi},
virtual Z before/after). F = |Tr(X^dag P U P)|/2. Usage: python truncacion_1q.py r T [M] [semillas]"""
import sys

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

r, T = float(sys.argv[1]), float(sys.argv[2])
M = int(sys.argv[3]) if len(sys.argv) > 3 else 16
semillas = int(sys.argv[4]) if len(sys.argv) > 4 else 12
Xq = np.array([[0, 1], [1, 0]], complex)
rng = np.random.default_rng(21)


def ops(L):
    b = np.diag(np.sqrt(np.arange(1, L)), 1)
    n = b.T @ b
    return b, -0.5 * n @ (n - np.eye(L)), (b + b.T) / 2, 1j * (b.T - b) / 2


def U_of(x, L, sub=1, eta=False):
    b, H0, Hx, Hy = ops(L)
    tau = T / M / sub
    amp, ph = r * np.tanh(x[:M]), x[M:2 * M]
    Za = np.diag(np.exp(1j * x[2 * M] * np.arange(L)))
    U, e = Za.copy(), 0.0
    for k in range(M):
        paso = expm(-1j * tau * (H0 + amp[k] * np.cos(ph[k]) * Hx + amp[k] * np.sin(ph[k]) * Hy))
        for _ in range(sub):
            U = paso @ U
            # Duhamel: residual sqrt(L)/2 |u| |c_{L-1}| per computational input; worst row norm over the block
            e += tau * np.sqrt(L) / 2 * abs(amp[k]) * np.linalg.norm(U[L - 1, :2])
    return np.diag(np.exp(1j * x[2 * M + 1] * np.arange(L))) @ U, e


LOPT = int(sys.argv[5]) if len(sys.argv) > 5 else 4          # dimension used in the optimization


def infid(x, L=LOPT):
    return 1 - abs(np.trace(Xq.conj().T @ U_of(x, L)[0][:2, :2])) / 2


best = None
for _ in range(semillas):
    x0 = np.concatenate([rng.normal(size=M) * 1.5 + 1.5, rng.uniform(0, 2 * np.pi, M), rng.uniform(0, 6.3, 2)])
    res = minimize(infid, x0, method='L-BFGS-B', options=dict(maxiter=3000))
    if best is None or res.fun < best.fun:
        best = res
    if best.fun < 1e-6:
        break
np.save(f'pulso_x_r{r}_T{T}_L{LOPT}.npy', best.x)
print(f'r = {r}, T = {T}/|delta| (= {T / (2 * np.pi):.2f} leakage periods), M = {M}: 1-F(L={LOPT}) = {best.fun:.2e}')
for L in (4, 5, 6, 8, 12):
    U, eta = U_of(best.x, L, sub=20)
    B = U[:2, :2]
    fug = 1 - np.linalg.norm(B, 'fro') ** 2 / 2
    print(f'  L = {L:2d}: 1-F = {1 - abs(np.trace(Xq.conj().T @ B)) / 2:.2e}, leakage = {fug:.1e}'
          + (f', Duhamel eta_L = {eta:.2e}' if L == 4 else ''))
