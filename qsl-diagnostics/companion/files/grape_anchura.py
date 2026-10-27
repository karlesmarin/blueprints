# encaje: control óptimo con tope de ANCHURA ESPECTRAL w(H(t)) <= Omega (H totalmente controlable) para comprobar la
# cota T >= dphi*/Omega de Nelson-Barnes (arXiv:2604.23031) cuando dphi* > pi (U_4d); investigación, no herramienta.
"""H_k = V_k diag(e_k) V_k^dag with eigenvalues e_k = (Omega/2) tanh(raw) in [-Omega/2, Omega/2] (width <= Omega),
V_k = expm(i herm(raw)); U = prod_k exp(-i tau H_k). Fidelity up to global phase: |Tr(G^dag U)| / n.
Targets: U_4d = exp(i pi/4 (2ZI + IZ)) (claimed T* = 3pi/(2 Omega)); CZ (T* = pi/Omega) as control.
Usage: python grape_anchura.py gate M T1,T2,... (T in units of pi/Omega) [semillas]"""
import sys

import numpy as np
import torch

torch.set_default_dtype(torch.float64)
puerta, M = sys.argv[1], int(sys.argv[2])
Ts = [float(x) * np.pi for x in sys.argv[3].split(',')]
semillas = int(sys.argv[4]) if len(sys.argv) > 4 else 12
Z = np.diag([1.0, -1.0])
I2 = np.eye(2)
if puerta == 'u4d':
    G = np.diag(np.exp(1j * np.pi / 4 * np.diag(2 * np.kron(Z, I2) + np.kron(I2, Z))))
else:
    G = np.diag([1, 1, 1, -1]).astype(complex)
n = 4
Gt = torch.tensor(G)
iu = torch.triu_indices(n, n, 1)
k = n * (n - 1) // 2


def herm(x):
    A = torch.zeros((n, n), dtype=torch.complex128).index_put((iu[0], iu[1]), torch.complex(x[:k], x[k:2 * k]))
    return A + A.conj().T + torch.diag(x[2 * k:2 * k + n].to(torch.complex128))


def U_of(x, T):
    U = torch.eye(n, dtype=torch.complex128)
    q, tau = 0, T / M
    for _ in range(M):
        V = torch.linalg.matrix_exp(1j * herm(x[q:q + n * n]))
        e = 0.5 * torch.tanh(x[q + n * n:q + n * n + n])          # Omega = 1
        H = V @ torch.diag(e.to(torch.complex128)) @ V.conj().T
        U = torch.linalg.matrix_exp(-1j * tau * H) @ U
        q += n * n + n
    return U


def infid(x, T):
    return 1 - torch.abs(torch.trace(Gt.conj().T @ U_of(x, T))) / n


npar = M * (n * n + n)
fases = np.angle(np.diag(G))
print(f'{puerta}: fases/pi = {np.round(fases / np.pi, 3)}, M = {M}, semillas = {semillas}', flush=True)
gen = torch.Generator().manual_seed(5)
for T in Ts:
    mejor = 1.0
    for _ in range(semillas):
        x = torch.randn(npar, generator=gen).requires_grad_()
        opt = torch.optim.LBFGS([x], lr=1, max_iter=3000, tolerance_grad=1e-12, tolerance_change=1e-15,
                                line_search_fn='strong_wolfe')

        def cierre():
            opt.zero_grad()
            f = infid(x, T)
            f.backward()
            return f
        opt.step(cierre)
        mejor = min(mejor, float(infid(x, T).detach()))
        if mejor < 1e-10:
            break
    print(f'  T = {T / np.pi:.3f} pi/Omega  ->  1-F = {mejor:.2e}', flush=True)
