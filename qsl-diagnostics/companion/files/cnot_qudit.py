# encaje: exploración numérica de la cota de la CNOT con niveles extra (qsl-hardware): m_d y la norma no local del
# acoplo; investigación (falsar antes de formalizar), no herramienta.
"""(1) m_d = max over local unitaries V = U1 x U2 (d-level each) of dist(0, W(P V^dag G P)), G = CNOT extended by the
identity outside the qubit subspace, P = projector on the qubit subspace (4-dim). dist(0, W(K)) =
max(0, max_theta lambda_min((e^{i theta} K + h.c.)/2)). Generalized MT then gives T >= arccos(m_d)/J.
Note: V acts after G; the witness psi lives in the qubit subspace, so only the compression matters.
(2) J_nl = min over Hermitian A, B of ||Hc - A x I - I x B|| for Hc = g (a + a^dag) x (a + a^dag) truncated at d.
Controls: m_2 for iSWAP must give arccos -> pi/2 (Basyildiz: tight); m_2 for CNOT should be 1/sqrt(2) (pi/4)."""
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(7)


def herm(n, x):
    """Hermitian n x n from n^2 real parameters."""
    A = np.zeros((n, n), complex)
    iu = np.triu_indices(n, 1)
    k = n * (n - 1) // 2
    A[iu] = x[:k] + 1j * x[k:2 * k]
    A = A + A.conj().T
    A[np.diag_indices(n)] = x[2 * k:2 * k + n]
    return A


def dist0(K, nth=360):
    th = np.linspace(0, 2 * np.pi, nth, endpoint=False)
    return max(0.0, max(np.linalg.eigvalsh((np.exp(1j * t) * K + np.exp(-1j * t) * K.conj().T) / 2)[0] for t in th))


def gate_ext(G2, d):
    """two-qubit gate G2 (4x4, basis 00,01,10,11) acting on the qubit subspace of two d-level systems, identity else."""
    D = d * d
    G = np.eye(D, dtype=complex)
    idx = [i * d + j for i in range(2) for j in range(2)]
    for a, ia in enumerate(idx):
        for b, ib in enumerate(idx):
            G[ia, ib] = G2[a, b]
    return G, idx


def m_d(G2, d, intentos=40, iters=300):
    G, idx = gate_ext(G2, d)
    P = np.zeros((d * d, 4))
    for a, ia in enumerate(idx):
        P[ia, a] = 1
    npar = d * d

    def menos(x):
        U1 = expm(1j * herm(d, x[:npar]))
        U2 = expm(1j * herm(d, x[npar:]))
        V = np.kron(U1, U2)
        K = P.T @ V.conj().T @ G @ P
        return -dist0(K, 120)

    mejor = 0.0
    for _ in range(intentos):
        r = minimize(menos, rng.normal(size=2 * npar) * 1.5, method='Nelder-Mead',
                     options=dict(maxiter=iters * 2 * npar, xatol=1e-6, fatol=1e-8))
        mejor = max(mejor, -r.fun)
    return mejor


CNOT = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], complex)
ISWAP = np.array([[1, 0, 0, 0], [0, 0, 1j, 0], [0, 1j, 0, 0], [0, 0, 0, 1]], complex)
for nombre, G2 in [('iSWAP', ISWAP), ('CNOT', CNOT)]:
    for d in (2, 3):
        m = m_d(G2, d, intentos=12 if d == 3 else 20)
        print(f'{nombre:6s} d={d}: m_d ~ {m:.4f}  ->  T >= arccos(m)/J = {np.arccos(min(m, 1)):.4f}/J '
              f'(pi/2 = 1.5708, pi/4 = 0.7854)', flush=True)

# (2) non-local norm of the capacitive transmon coupling
for d in (2, 3, 4):
    a = np.diag(np.sqrt(np.arange(1, d)), 1)
    x = a + a.T
    Hc = np.kron(x, x)
    n0 = np.linalg.norm(Hc, 2)

    def f(p):
        return np.linalg.norm(Hc - np.kron(herm(d, p[:d * d]), np.eye(d)) - np.kron(np.eye(d), herm(d, p[d * d:])), 2)

    best = min(minimize(f, rng.normal(size=2 * d * d) * 0.1, method='Nelder-Mead',
                        options=dict(maxiter=20000, xatol=1e-8, fatol=1e-10)).fun for _ in range(6))
    print(f'acoplo capacitivo d={d}: ||Hc|| = {n0:.4f} g;  norma no local min_L ||Hc - L|| ~ {best:.4f} g', flush=True)
