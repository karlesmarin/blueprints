# encaje: control óptimo de la CNOT por resonancia cruzada con amplitud acotada |Omega_CR| <= r*Delta (qsl-hardware):
# tiempo mínimo con error < 1e-3 en función de r, parámetros medianos de IBM; investigación, no herramienta.
"""Two 3-level transmons, frame rotating at the TARGET frequency for both (time-independent): units Delta = 1,
H = Delta n_c + (dc/2) n_c(n_c-1) + (dt/2) n_t(n_t-1) + J (b_c^dag b_t + h.c.) + Re/Im(W_c)(b_c terms) + Re/Im(W_t)
(b_t terms); W_c piecewise constant, |W_c| <= r (tanh), W_t piecewise, |W_t| <= 0.1 * |dt| (as IBM single-qubit
rule). Free single-qubit SU(2) on each qubit block before and after. F = |Tr(CNOT^dag P U P)| / 4 (leakage lowers F).
IBM medians: J/Delta = 0.0176, delta/Delta = -2.7. Reference: first-order nu_ZX = J r (dc/(dc+Delta)) ->
T ~ pi/(2 nu_ZX) for a square CR pulse (ZX angle pi/2, H = nu/2 ZX)."""
import sys

import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(13)
_cli = __name__ == '__main__'                              # imported (grape_cr_continuacion.py): defaults
M = int(sys.argv[1]) if _cli and len(sys.argv) > 1 else 10
rs = [float(x) for x in sys.argv[2].split(',')] if _cli and len(sys.argv) > 2 else [0.25, 0.45, 0.7, 1.0, 1.5]
J, dc, dtt = 0.0176, -2.7, -2.7
d = 3
b = np.diag(np.sqrt(np.arange(1, d)), 1)
I = np.eye(d)
bc, bt = np.kron(b, I), np.kron(I, b)
nc, nt = bc.T @ bc, bt.T @ bt
H0 = nc + dc / 2 * nc @ (nc - np.eye(9)) + dtt / 2 * nt @ (nt - np.eye(9)) + J * (bc.T @ bt + bt.T @ bc)
Xc, Yc = (bc + bc.T) / 2, 1j * (bc.T - bc) / 2
Xt, Yt = (bt + bt.T) / 2, 1j * (bt.T - bt) / 2
idx = [0, 1, 3, 4]
CNOT = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], complex)
s = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.diag([1.0, -1.0]).astype(complex)]


def su2(v):
    return expm(1j * sum(v[i] * s[i] for i in range(3)))


def emb(u):
    """2x2 on qubit levels of a 3-level system, identity on |2>."""
    E = np.eye(3, dtype=complex)
    E[:2, :2] = u
    return E


def U_of(x, T, r):
    tau = T / M
    ac, pc = r * np.tanh(x[:M]), x[M:2 * M]
    at, pt = 0.1 * abs(dtt) * np.tanh(x[2 * M:3 * M]), x[3 * M:4 * M]
    U = np.eye(9, dtype=complex)
    for k in range(M):
        H = H0 + ac[k] * (np.cos(pc[k]) * Xc + np.sin(pc[k]) * Yc) + at[k] * (np.cos(pt[k]) * Xt + np.sin(pt[k]) * Yt)
        U = expm(-1j * tau * H) @ U
    q = 4 * M
    pre = np.kron(emb(su2(x[q:q + 3])), emb(su2(x[q + 3:q + 6])))
    post = np.kron(emb(su2(x[q + 6:q + 9])), emb(su2(x[q + 9:q + 12])))
    return post @ U @ pre


def infid(x, T, r):
    B = U_of(x, T, r)[np.ix_(idx, idx)]
    return 1 - abs(np.trace(CNOT.conj().T @ B)) / 4


def mejor(T, r, intentos=6):
    m = 1.0
    for _ in range(intentos):
        x0 = np.concatenate([rng.normal(size=M) + 2, rng.uniform(0, 6.3, M), rng.normal(size=M) * 0.5,
                             rng.uniform(0, 6.3, M), rng.normal(size=12)])
        res = minimize(infid, x0, args=(T, r), method='L-BFGS-B', options=dict(maxiter=2500))
        m = min(m, res.fun)
        if m < 1e-4:
            break
    return m


if __name__ == '__main__':
    print(f'J/Delta = {J}, delta/Delta = {dc}, M = {M}; pi/(2J) (cota de intercambio) = {np.pi / (2 * J):.1f}/Delta',
          flush=True)
for r in (rs if __name__ == '__main__' else []):
    nu = J * r * abs(dc / (dc + 1))
    Tref = np.pi / (2 * nu)
    # 27-oct: for r >= 0.7 the first-order Tref falls BELOW the exchange limit pi/(2J), so a grid in units of Tref never
    # reached the feasible region; with a 3rd argument 'abs' the grid is in units of pi/(2J)
    if len(sys.argv) > 3 and sys.argv[3] == 'abs':
        rejilla = [np.pi / (2 * J) * f for f in (1.0, 1.15, 1.3, 1.5, 1.8, 2.2)]
    else:
        rejilla = [Tref * f for f in (0.3, 0.45, 0.6, 0.75, 0.9, 1.05, 1.3)]
    res = None
    for T in rejilla:
        e = mejor(T, r)
        if e < 1e-3:
            res = (T, e)
            break
    if res:
        print(f'  r = Omega_CR/Delta = {r:.2f}: T_min ~ {res[0]:7.1f}/Delta = {res[0] / Tref:.2f} x pi/(2 nu_ZX) = '
              f'{res[0] * 2 * J / np.pi:.2f} x pi/(2J)  (1-F = {res[1]:.1e})', flush=True)
    else:
        print(f'  r = {r:.2f}: sin CNOT con 1-F < 1e-3 hasta T = {rejilla[-1]:.1f}/Delta '
              f'(= {rejilla[-1] * 2 * J / np.pi:.2f} x pi/(2J))', flush=True)
