# encaje: tiempo mínimo para crear un estado de Bell desde un producto con acoplo fijo, control local ilimitado y
# ancillas locales, con GRADIENTE EXACTO (torch); compara el mejor coeficiente de Schmidt con cos(c T) (qsl-hardware).
"""Same model as grape_bell.py (heis XX+YY+ZZ, ising ZZ, xy (XX+YY)/2 on the two main qubits; ancilla dim da per side).
Objective: smallest achievable largest Schmidt coefficient lambda(T) of psi(T) across A|B (smooth surrogate: we
minimise the purity sum s_i^4 and report s_max; then a short refinement on s_max itself).
Prediction tested (identity seen in grape_bell.py output): lambda(T) = cos(w T) with w = (E_max - E_min)/2 of Hc
(heis: 2, ising: 1, xy: 1), independent of the ancilla. Usage: python grape_bell_torch.py tipo da M T1,T2 [semillas]"""
import sys

import numpy as np
import torch

torch.set_default_dtype(torch.float64)
tipo, da, M = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
Ts = [float(x) for x in sys.argv[4].split(',')]
semillas = int(sys.argv[5]) if len(sys.argv) > 5 else 16
X = np.array([[0, 1], [1, 0]], complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1.0, -1.0]).astype(complex)
pares = {'heis': [(X, X), (Y, Y), (Z, Z)], 'ising': [(Z, Z)],
         'xy': [(X / np.sqrt(2), X / np.sqrt(2)), (Y / np.sqrt(2), Y / np.sqrt(2))]}[tipo]
Ia = np.eye(da)
D = 2 * da
Hc_np = sum(np.kron(np.kron(P, Ia), np.kron(Q, Ia)) for P, Q in pares)
ev = np.linalg.eigvalsh(Hc_np)
w = (ev[-1] - ev[0]) / 2
Hc = torch.tensor(Hc_np)
ID = torch.eye(D, dtype=torch.complex128)
psi0 = torch.zeros(D * D, dtype=torch.complex128)
psi0[0] = 1
n, k = D * D, D * (D - 1) // 2
iu = torch.triu_indices(D, D, 1)


def herm(x):
    A = torch.zeros((D, D), dtype=torch.complex128).index_put((iu[0], iu[1]), torch.complex(x[:k], x[k:2 * k]))
    return A + A.conj().T + torch.diag(x[2 * k:2 * k + D].to(torch.complex128))


def schmidt(x, T):
    psi = torch.kron(torch.linalg.matrix_exp(1j * herm(x[0:n])), torch.linalg.matrix_exp(1j * herm(x[n:2 * n]))) @ psi0
    q = 2 * n
    for _ in range(M):
        L = torch.kron(herm(x[q:q + n]), ID) + torch.kron(ID, herm(x[q + n:q + 2 * n]))
        q += 2 * n
        psi = torch.linalg.matrix_exp(-1j * (T / M) * (L + Hc)) @ psi
    return torch.linalg.svdvals(psi.reshape(D, D))


def correr(x, T, f):
    opt = torch.optim.LBFGS([x], lr=1, max_iter=3000, tolerance_grad=1e-12, tolerance_change=1e-15,
                            line_search_fn='strong_wolfe')

    def cierre():
        opt.zero_grad()
        v = f(schmidt(x, T))
        v.backward()
        return v
    opt.step(cierre)


npar = 2 * n + M * 2 * n
print(f'{tipo}, da = {da}, M = {M}, ||Hc|| = {np.linalg.norm(Hc_np, 2):.3f}, w = (Emax-Emin)/2 = {w:.3f}, '
      f'parámetros {npar}', flush=True)
gen = torch.Generator().manual_seed(11)
for T in Ts:
    mejor = 1.0
    for _ in range(semillas):
        x = (torch.randn(npar, generator=gen) * 0.8).requires_grad_()
        correr(x, T, lambda s: (s ** 4).sum())
        correr(x, T, lambda s: s[0])
        mejor = min(mejor, float(schmidt(x, T)[0].detach()))
    pred = np.cos(w * T) if w * T < np.pi / 4 else 1 / np.sqrt(2)
    print(f'  T = {T:.4f}: lambda = {mejor:.6f}   cos(wT) = {np.cos(w * T):.6f}   diferencia {mejor - pred:+.1e}',
          flush=True)
