# encaje: control óptimo de la puerta X en un transmón (Duffing de L niveles) con amplitud acotada |Omega| <= r*|delta|:
# tiempo mínimo con error < 1e-4 (fuga incluida) en función de r (qsl-hardware); investigación, no herramienta.
"""Rotating frame at the qubit frequency, units |delta| = 1: H(t) = (delta/2) n(n-1) + Re(W)/2 (b + b^dag)
+ Im(W)/2 i(b^dag - b), W(t) = r * tanh(u) e^{i phi} piecewise constant (M segments) so |W| <= r. Virtual Z frames
before/after are free (two angles). Fidelity F = |Tr(X^dag P U P)| / 2 on the qubit block (leakage lowers F).
For each r: smallest T on a grid with 1 - F < 1e-4. Control: L = 2 must give T* = pi / r."""
import sys

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(9)
L = int(sys.argv[1]) if len(sys.argv) > 1 else 4
M = int(sys.argv[2]) if len(sys.argv) > 2 else 16
rs = [float(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0.1, 0.2, 0.3, 0.5, 0.8, 1.0]
b = np.diag(np.sqrt(np.arange(1, L)), 1)
n = b.T @ b
H0 = -0.5 * n @ (n - np.eye(L))          # delta = -1 (transmon)
Hx, Hy = (b + b.T) / 2, 1j * (b.T - b) / 2
Xq = np.array([[0, 1], [1, 0]], complex)


def U_of(x, T, r):
    tau = T / M
    amp = r * np.tanh(x[:M])
    ph = x[M:2 * M]
    U = np.eye(L, dtype=complex)
    for k in range(M):
        U = expm(-1j * tau * (H0 + amp[k] * np.cos(ph[k]) * Hx + amp[k] * np.sin(ph[k]) * Hy)) @ U
    za, zb = x[2 * M], x[2 * M + 1]
    Za = np.diag(np.exp(1j * za * np.arange(L)))
    Zb = np.diag(np.exp(1j * zb * np.arange(L)))
    return Zb @ U @ Za


def infid(x, T, r):
    B = U_of(x, T, r)[:2, :2]
    return 1 - abs(np.trace(Xq.conj().T @ B)) / 2


def mejor(T, r, intentos=10):
    m = 1.0
    for _ in range(intentos):
        x0 = np.concatenate([rng.normal(size=M) * 1.5 + 1.5, rng.uniform(0, 2 * np.pi, M), rng.uniform(0, 6.3, 2)])
        res = minimize(infid, x0, args=(T, r), method='L-BFGS-B', options=dict(maxiter=3000))
        m = min(m, res.fun)
        if m < 1e-5:
            break
    return m


print(f'L = {L} niveles, M = {M} tramos; unidades |delta| = 1; objetivo 1 - F < 1e-4', flush=True)
for r in rs:
    tq = np.pi / r                          # two-level speed limit at amplitude r
    rejilla = [tq * f for f in (1.0, 1.05, 1.15, 1.3, 1.5, 1.8, 2.2, 2.7, 3.5, 4.5, 6.0)]
    T_ok = None
    for T in rejilla:
        e = mejor(T, r)
        if e < 1e-4:
            T_ok = (T, e)
            break
    if T_ok:
        T, e = T_ok
        print(f'  r = Omega_max/|delta| = {r:.2f}: T_min ~ {T:7.2f}/|delta| = {T / tq:.2f} x pi/Omega_max = '
              f'{T / (2 * np.pi):.2f} periodos de fuga (1-F = {e:.1e})', flush=True)
    else:
        print(f'  r = {r:.2f}: sin puerta con 1-F < 1e-4 hasta T = {rejilla[-1]:.1f}', flush=True)
