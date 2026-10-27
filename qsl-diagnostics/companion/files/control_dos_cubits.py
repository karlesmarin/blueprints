# encaje: controles numéricos de la cota certificada de dos cúbits (TwoQubitEntangling.lean, en curso): la cota nunca
# supera el tiempo alcanzable y la desigualdad de Duhamel se cumple en evoluciones aleatorias; investigación.
"""1. Exchange coupling H = J (s+ s- + s- s+) = (J/2)(XX + YY): from |01>, the state at time t is
   cos(Jt)|01> - i sin(Jt)|10>, maximally entangled first at t* = pi/(4J). The certified bound sqrt(2 - sqrt 2)/J must
   be <= t* (if not, the theorem would be false).
2. Duhamel: ||exp(X+Y) - exp(X)|| <= ||Y|| for random skew-Hermitian X, Y (operator 2-norm); count violations.
3. Piecewise evolutions with random local controls and ||H|| = J: the maximal overlap with a maximally entangled state,
   reached from a product state, never exceeds what time sum(tau)*J allows (distance >= sqrt(2 - sqrt 2) needs
   J*T >= sqrt(2 - sqrt 2))."""
import numpy as np
from scipy.linalg import expm

rng = np.random.default_rng(1)
X = np.array([[0, 1], [1, 0]], complex)
Y = np.array([[0, -1j], [1j, 0]])
Z = np.diag([1, -1]).astype(complex)
I2 = np.eye(2)
cota = np.sqrt(2 - np.sqrt(2))

J = 1.0
H = J / 2 * (np.kron(X, X) + np.kron(Y, Y))
psi0 = np.zeros(4, complex)
psi0[1] = 1                      # |01>


def concurrence(psi):
    return 2 * abs(psi[0] * psi[3] - psi[1] * psi[2])


from scipy.optimize import brentq  # noqa: E402

ts = np.linspace(0, 1.2, 1201)
c = np.array([concurrence(expm(-1j * H * t) @ psi0) for t in ts])
# 27-oct: the first version searched c >= 1 - 1e-9 on a 1e-3 grid, never met (argmax of all-False = 0): take the
# first maximum of the concurrence on the grid and refine the zero of d/dt by brentq
i = int(np.argmax(c))
dc = lambda t: concurrence(expm(-1j * H * (t + 1e-7)) @ psi0) - concurrence(expm(-1j * H * (t - 1e-7)) @ psi0)
t_star = brentq(dc, ts[i - 1], ts[i + 1])
print(f'   concurrencia máxima {concurrence(expm(-1j * H * t_star) @ psi0):.12f} en t = {t_star:.6f}')
print(f'1. tiempo alcanzable al entrelazamiento máximo: {t_star:.4f}/J (pi/4 = {np.pi / 4:.4f});'
      f' cota certificada {cota:.4f}/J;', 'COTA <= ALCANZABLE: OK' if cota <= t_star + 1e-9 else 'FALLA: COTA FALSA')
print(f'   holgura de la cota: {t_star / cota:.4f} (1 = ajustada)')


def skew(n):
    A = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    return (A - A.conj().T) / 2


viol, peor = 0, 0.0
for _ in range(20000):
    Xm, Ym = skew(4) * rng.uniform(0, 5), skew(4) * rng.uniform(0, 2)
    lhs = np.linalg.norm(expm(Xm + Ym) - expm(Xm), 2)
    rhs = np.linalg.norm(Ym, 2)
    peor = max(peor, lhs / rhs)
    viol += lhs > rhs + 1e-10
print(f'2. Duhamel en 20000 pares aleatorios: violaciones {viol}; máximo de ||e^(X+Y)-e^X||/||Y|| = {peor:.6f}')


def herm(n):
    A = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    return (A + A.conj().T) / 2


bell = np.array([1, 0, 0, 1], complex) / np.sqrt(2)
mal = 0
for _ in range(3000):
    Hi = herm(4)
    Hi *= J / np.linalg.norm(Hi, 2)
    U = np.eye(4, dtype=complex)
    T = 0.0
    for _ in range(rng.integers(1, 6)):
        tau = rng.uniform(0, 0.3)
        L = np.kron(herm(2) * 5, I2) + np.kron(I2, herm(2) * 5)
        U = expm(-1j * tau * (L + Hi)) @ U
        T += tau
    a = rng.normal(size=2) + 1j * rng.normal(size=2)
    b = rng.normal(size=2) + 1j * rng.normal(size=2)
    v = np.kron(a / np.linalg.norm(a), b / np.linalg.norm(b))
    d = np.linalg.norm(U @ v - bell)   # distance to Bell reached from a product state
    # theorem: if d were 0 then J*T >= cota; contrapositive check: J*T < cota  ==>  d > 0, quantitatively
    # d >= cota - J*T (product-to-product within J*T, product at distance >= cota from Bell)
    if d < cota - J * T - 1e-9:
        mal += 1
print(f'3. evoluciones con control local aleatorio: violaciones de d >= sqrt(2-sqrt2) - J T: {mal} de 3000')
