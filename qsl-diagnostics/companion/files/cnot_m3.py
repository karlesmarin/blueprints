# encaje: m_d para la CNOT con mejor optimización (sigue a cnot_qudit.py, que no convergió en d = 3); investigación.
"""m_d = max over local unitaries V of dist(0, W(P V^dag G P)). Conjecture: m_d = 1/sqrt(2) for every d.
Improvements over cnot_qudit.py: finer theta grid + golden refinement in dist0; optimizer = Powell then BFGS from
(a) random starts and (b) WARM starts = the best d = 2 optimum embedded as U (+) 1 (so m_3 >= m_2 is guaranteed
numerically too). Control: m_2 must reach 1/sqrt 2 = 0.70711."""
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize, minimize_scalar

rng = np.random.default_rng(11)
OBJ = 1 / np.sqrt(2)


def herm(n, x):
    A = np.zeros((n, n), complex)
    iu = np.triu_indices(n, 1)
    k = n * (n - 1) // 2
    A[iu] = x[:k] + 1j * x[k:2 * k]
    A = A + A.conj().T
    A[np.diag_indices(n)] = x[2 * k:2 * k + n]
    return A


def dist0(K):
    f = lambda t: -np.linalg.eigvalsh((np.exp(1j * t) * K + np.exp(-1j * t) * K.conj().T) / 2)[0]
    th = np.linspace(0, 2 * np.pi, 240, endpoint=False)
    v = [f(t) for t in th]
    i = int(np.argmin(v))
    paso = th[1] - th[0]   # 27-oct: a bracket built from th[i-1], th[i+1] is unordered at i = 0 or the last point
    r = minimize_scalar(f, bounds=(th[i] - paso, th[i] + paso), method='bounded', options=dict(xatol=1e-10))
    return max(0.0, -min(r.fun, v[i]))


CNOT = np.array([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], complex)


def preparar(d):
    G = np.eye(d * d, dtype=complex)
    idx = [i * d + j for i in range(2) for j in range(2)]
    for a, ia in enumerate(idx):
        for b, ib in enumerate(idx):
            G[ia, ib] = CNOT[a, b]
    P = np.zeros((d * d, 4))
    for a, ia in enumerate(idx):
        P[ia, a] = 1
    return G, P


def objetivo(d):
    G, P = preparar(d)
    n = d * d

    def f(x):
        V = np.kron(expm(1j * herm(d, x[:n])), expm(1j * herm(d, x[n:])))
        return -dist0(P.T @ V.conj().T @ G @ P)
    return f


def optimizar(f, x0):
    r = minimize(f, x0, method='Powell', options=dict(maxiter=40000, xtol=1e-7, ftol=1e-10))
    r2 = minimize(f, r.x, method='BFGS', options=dict(maxiter=2000, gtol=1e-9))
    return (r2 if r2.fun < r.fun else r)


# d = 2
f2 = objetivo(2)
mejores2 = sorted((optimizar(f2, rng.normal(size=8) * 1.5) for _ in range(25)), key=lambda r: r.fun)
m2, x2 = -mejores2[0].fun, mejores2[0].x
print(f'd=2: m_2 = {m2:.6f}  (1/sqrt2 = {OBJ:.6f})', 'OK' if abs(m2 - OBJ) < 1e-3 else 'NO CONVERGE', flush=True)


def embeber(x):
    """d=2 parameters (4 + 4) -> d=3 parameters (9 + 9) with the same 2x2 block and 0 on level 2."""
    def una(p):
        # herm(2): [Re(01), Im(01), diag0, diag1]; herm(3): [Re(01),Re(02),Re(12), Im(01),Im(02),Im(12), d0,d1,d2]
        return np.array([p[0], 0, 0, p[1], 0, 0, p[2], p[3], 0.0])
    return np.concatenate([una(x[:4]), una(x[4:])])


f3 = objetivo(3)
xw = embeber(x2)
print(f'd=3 control: arranque embebido da {-f3(xw):.6f} (debe = m_2)', flush=True)
res = []
for k in range(30):
    x0 = xw + rng.normal(size=18) * (0.05 if k < 15 else 0.6)    # warm starts + perturbed
    res.append(optimizar(f3, x0))
for k in range(15):
    res.append(optimizar(f3, rng.normal(size=18) * 1.5))         # cold starts
m3 = max(-r.fun for r in res)
print(f'd=3: m_3 = {m3:.6f}  ->  T >= arccos(m_3)/J = {np.arccos(min(m3, 1)):.6f}/J  (pi/4 = {np.pi / 4:.6f})')
print('CONJETURA m_3 = 1/sqrt2:', 'se sostiene (no supera)' if m3 <= OBJ + 1e-4 else f'FALLA: m_3 supera 1/sqrt2 en {m3 - OBJ:.2e}')
