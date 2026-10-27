# encaje: verificación propia de la cota refinada de la CZ con qutrits (27-oct):
# lema max_{P_A,P_B rango 2} Tr[(P_A x P_B) Hc^2]/4 = 97/32 (J=1), caso de igualdad, y la cota temporal resultante;
# además prueba la cota contra la tabla numérica (T = 0.45, 0.50, 0.55). Investigación, no herramienta.
import numpy as np
from scipy.optimize import minimize

d = 3
a = np.diag(np.sqrt(np.arange(1, d)), 1)
Hc = np.kron(a.T, a) + np.kron(a, a.T)
H2 = Hc @ Hc


def proj(x):
    """rank-2 projector I - |v><v| from a complex unit v (parametrized by 6 reals)"""
    v = x[:3] + 1j * x[3:6]
    v = v / np.linalg.norm(v)
    return np.eye(d) - np.outer(v, v.conj())


def menos_val(x):
    PA, PB = proj(x[:6]), proj(x[6:])
    return -np.real(np.trace(np.kron(PA, PB) @ H2)) / 4


rng = np.random.default_rng(1)
mejor = 0.0
for _ in range(300):
    r = minimize(menos_val, rng.normal(size=12), method='L-BFGS-B')
    mejor = max(mejor, -r.fun)
print(f'lema: max Tr[(PA x PB) Hc^2]/4 over 300 random starts = {mejor:.10f}; 97/32 = {97 / 32:.10f}')
v = np.array([np.sqrt(7 / 8), 0, np.sqrt(1 / 8)])
P = np.eye(d) - np.outer(v, v)
rho = np.kron(P, P) / 4
print(f'igualdad: <Hc^2> = {np.real(np.trace(rho @ H2)):.10f}, <Hc> = {np.real(np.trace(rho @ Hc)):.2e}')
# brute-force sanity over random projectors (no optimizer)
vals = [np.real(np.trace(np.kron(proj(rng.normal(size=6)), proj(rng.normal(size=6))) @ H2)) / 4 for _ in range(200000)]
print(f'muestreo aleatorio 2e5: max = {max(vals):.6f} (debe ser <= 97/32)')
c = np.sqrt(97 / 32)
for e in (0, 2e-8, 1e-4):
    print(f'cota: e = {e}: J T >= {(np.pi / 4 - np.arccos(1 - e)) / c:.7f}  (antigua {(np.pi / 4 - np.arccos(1 - e)) / 2:.7f})')
for T, e_found in ((0.45, 5.0e-3), (0.50, 3.7e-4), (0.55, 2e-8)):
    emin = 1 - np.cos(max(np.pi / 4 - T * c, 0))
    print(f'T = {T}/J: error mínimo posible e >= {emin:.3e}; hallado {e_found:.1e} -> {"compatible" if e_found >= emin else "CONTRADICE"}')
print(f'construcción pi/6 frente a la cota: {(np.pi / 6) / (np.pi / 4 / c):.4f}')
