# encaje: re-evalua SIN reoptimizar los pulsos X guardados de truncacion_1q.py (r=1 T=7 con 4 y 6 niveles; r=0.351 T=10) con L=4,5,6,8,12 y el certificado de Duhamel eta4; rapido y determinista. Investigacion.
import numpy as np
from scipy.linalg import expm
from pathlib import Path
D = Path(__file__).parent
Xq = np.array([[0, 1], [1, 0]], complex)


def run(fn, r, T, L, M=16, sub=20):
    x = np.load(D / fn)
    b = np.diag(np.sqrt(np.arange(1, L)), 1)
    n = b.T @ b
    H0, Hx, Hy = -0.5 * n @ (n - np.eye(L)), (b + b.T) / 2, 1j * (b.T - b) / 2
    tau = T / M / sub
    amp, ph = r * np.tanh(x[:M]), x[M:2 * M]
    U, e = np.diag(np.exp(1j * x[2 * M] * np.arange(L))), 0.0
    for k in range(M):
        p = expm(-1j * tau * (H0 + amp[k] * np.cos(ph[k]) * Hx + amp[k] * np.sin(ph[k]) * Hy))
        for _ in range(sub):
            U = p @ U
            e += tau * np.sqrt(L) / 2 * abs(amp[k]) * np.linalg.norm(U[L - 1, :2])
    U = np.diag(np.exp(1j * x[2 * M + 1] * np.arange(L))) @ U
    return 1 - abs(np.trace(Xq.conj().T @ U[:2, :2])) / 2, e


for fn, r, T in (('pulso_x_r1.0_T7.0_L4.npy', 1.0, 7.0), ('pulso_x_r1.0_T7.0_L6.npy', 1.0, 7.0),
                 ('pulso_x_r0.351_T10.0_L6.npy', 0.351, 10.0)):
    for L in (4, 5, 6, 8, 12):
        f, e = run(fn, r, T, L)
        print(fn, 'L', L, '1-F %.2e' % f, ('eta4 %.3f' % e) if L == 4 else '')
