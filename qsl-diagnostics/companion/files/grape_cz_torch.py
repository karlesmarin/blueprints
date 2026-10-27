# encaje: control óptimo con GRADIENTE EXACTO (autograd de torch) del tiempo mínimo de una CZ con niveles extra bajo
# intercambio J (b1^dag b2 + h.c.); sustituye al gradiente numérico de grape_cz.py (lento); investigación, no herramienta.
"""Same model as grape_cz.py: U = Upost * prod_k exp(-i tau (A_k x I + I x B_k + Hc)) * Upre, local A_k, B_k Hermitian
d x d, Upre/Upost arbitrary local unitaries; F = |Tr(CZ^dag P U P)| / 4 (1 iff the qubit block is CZ up to a phase and
nothing leaks). Optional cap: every local Hamiltonian is rescaled to spectral norm <= amax (units of J) via a smooth
tanh map, so 'unbounded' = amax None. Usage: python grape_cz_torch.py d M T1,T2,... [amax] [semillas]
Controls: d = 2 must need T ~ pi/2 (Howard App. C); the bound T >= pi/(4||Hc||) must never be beaten; every best
solution is re-checked with scipy expm in float64 (independent of torch) and its leakage out of P is printed."""
import sys

import numpy as np
import torch
from scipy.linalg import expm

torch.set_default_dtype(torch.float64)
d = int(sys.argv[1])
M = int(sys.argv[2])
Ts = [float(x) for x in sys.argv[3].split(',')]
amax = float(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != 'none' else None
semillas = int(sys.argv[5]) if len(sys.argv) > 5 else 12
b = np.diag(np.sqrt(np.arange(1, d)), 1)
Hc_np = np.kron(b.T, b) + np.kron(b, b.T)
nH = np.linalg.norm(Hc_np, 2)
Hc = torch.tensor(Hc_np, dtype=torch.complex128)
Id = torch.eye(d, dtype=torch.complex128)
idx = [i * d + j for i in range(2) for j in range(2)]
CZ = torch.diag(torch.tensor([1, 1, 1, -1], dtype=torch.complex128))
n = d * d
k = d * (d - 1) // 2
iu = torch.triu_indices(d, d, 1)


def herm(x):
    A = torch.zeros((d, d), dtype=torch.complex128)
    A = A.index_put((iu[0], iu[1]), torch.complex(x[:k], x[k:2 * k]))
    return A + A.conj().T + torch.diag(x[2 * k:2 * k + d].to(torch.complex128))


def acotar(A):
    if amax is None:
        return A
    s = torch.linalg.matrix_norm(A, 2) + 1e-12
    return A * (amax * torch.tanh(s / amax) / s)


def piezas(x):
    """local Hermitian generators from the parameter vector (for the torch run and for the scipy re-check)"""
    pre = [herm(x[0:n]), herm(x[n:2 * n])]
    post = [herm(x[2 * n:3 * n]), herm(x[3 * n:4 * n])]
    seg, q = [], 4 * n
    for _ in range(M):
        seg.append((acotar(herm(x[q:q + n])), acotar(herm(x[q + n:q + 2 * n]))))
        q += 2 * n
    return pre, post, seg


def U_of(x, T):
    pre, post, seg = piezas(x)
    U = torch.kron(torch.linalg.matrix_exp(1j * pre[0]), torch.linalg.matrix_exp(1j * pre[1]))
    for A, B in seg:
        U = torch.linalg.matrix_exp(-1j * (T / M) * (torch.kron(A, Id) + torch.kron(Id, B) + Hc)) @ U
    return torch.kron(torch.linalg.matrix_exp(1j * post[0]), torch.linalg.matrix_exp(1j * post[1])) @ U


def infid(x, T):
    B = U_of(x, T)[idx][:, idx]
    return 1 - torch.abs(torch.trace(CZ.conj().T @ B)) / 4


def recheck(x, T):
    """independent float64 evaluation with scipy.linalg.expm; returns (1-F, leakage of the qubit subspace)"""
    pre, post, seg = piezas(x)
    a = lambda t: t.detach().numpy()
    U = np.kron(expm(1j * a(pre[0])), expm(1j * a(pre[1])))
    for A, B in seg:
        U = expm(-1j * (T / M) * (np.kron(a(A), np.eye(d)) + np.kron(np.eye(d), a(B)) + Hc_np)) @ U
    U = np.kron(expm(1j * a(post[0])), expm(1j * a(post[1]))) @ U
    Bq = U[np.ix_(idx, idx)]
    fuga = 1 - np.linalg.norm(Bq, 'fro') ** 2 / 4
    picos = max(max(np.linalg.norm(a(A), 2), np.linalg.norm(a(B), 2)) for A, B in seg)
    return 1 - abs(np.trace(np.diag([1, 1, 1, -1]).conj().T @ Bq)) / 4, fuga, picos


npar = 4 * n + M * 2 * n
print(f'd={d}, M={M}, ||Hc|| = {nH:.4f}, cota pi/(4||Hc||) = {np.pi / (4 * nH):.4f}, amax = {amax}, '
      f'parámetros {npar}, semillas {semillas}', flush=True)
gen = torch.Generator().manual_seed(7)
for T in Ts:
    mejor, xb = 1.0, None
    for s in range(semillas):
        x = (torch.randn(npar, generator=gen) * 0.8).requires_grad_()
        opt = torch.optim.LBFGS([x], lr=1, max_iter=4000, tolerance_grad=1e-12, tolerance_change=1e-15,
                                line_search_fn='strong_wolfe')

        def cierre():
            opt.zero_grad()
            f = infid(x, T)
            f.backward()
            return f
        opt.step(cierre)
        f = float(infid(x, T))
        if f < mejor:
            mejor, xb = f, x.detach().clone()
        if mejor < 1e-10:
            break
    r, fuga, picos = recheck(xb, T)
    print(f'  T = {T:.4f}/J ({T / (np.pi / 2):.3f} x pi/2)  ->  1-F = {mejor:.2e}  | scipy: 1-F = {r:.2e}, '
          f'fuga = {fuga:.1e}, max ||A_k|| = {picos:.1f} J', flush=True)
    np.save(f'cz_best_d{d}_M{M}_T{T:.4f}_a{amax}.npy', xb.numpy())
