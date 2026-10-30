"""Tiempo mínimo de la transferencia cúbit → modo → cúbit con acoplamientos acotados |g1|, |g2| <= g.
# encaje: investigación (qsl-hardware v2, relevo de IBM arXiv 2610.29986); numérico, sin fuerza de prueba.

Modelo de una excitación, resonante: H(t) = g1(t)(|a><b| + h.c.) + g2(t)(|b><c| + h.c.). Unidades g = 1.
Para cada T se maximiza la población final en |c> con controles constantes a trozos (N trozos) y se busca el menor
T con población 1. Variante A: g1, g2 reales en [-1, 1]. Variante B: complejos con |g_i| <= 1.
Referencias a contrastar: ambos acoplamientos al máximo dan π/√2 ≈ 2.2214; dos saltos sucesivos, π; cota
certificada (Lean, fsAngle_le_time_halfWidth) π/(2√2) ≈ 1.1107.
"""
import numpy as np
from scipy.optimize import minimize
from scipy.linalg import expm


def H(g1, g2):
    return np.array([[0, g1, 0], [np.conj(g1), 0, g2], [0, np.conj(g2), 0]], dtype=complex)


def poblacion(params, T, N, complejo):
    if complejo:
        r1, p1, r2, p2 = np.split(params, 4)
        g1 = np.tanh(r1) * np.exp(1j * p1); g2 = np.tanh(r2) * np.exp(1j * p2)
    else:
        r1, r2 = np.split(params, 2)
        g1, g2 = np.tanh(r1), np.tanh(r2)
    psi = np.array([1, 0, 0], dtype=complex)
    dt = T / N
    for k in range(N):
        psi = expm(-1j * dt * H(g1[k], g2[k])) @ psi
    return abs(psi[2]) ** 2


def mejor(T, N, complejo, intentos=12, semilla=0):
    rng = np.random.default_rng(semilla)
    k = 4 if complejo else 2
    best = 0.0
    for _ in range(intentos):
        x0 = rng.normal(0, 2, k * N)
        r = minimize(lambda p: -poblacion(p, T, N, complejo), x0, method='L-BFGS-B', options=dict(maxiter=400))
        best = max(best, -r.fun)
        if best > 1 - 1e-10:
            break
    return best


for complejo in (False, True):
    print("variante", "B (complejos)" if complejo else "A (reales)", flush=True)
    for T in [1.2, 1.6, 1.9, 2.0, 2.1, 2.15, 2.2, 2.2214, 2.25, 2.4]:
        p = mejor(T, N=24, complejo=complejo)
        print(f"  T·g = {T:.4f}: población máxima en |c> = {p:.8f}", flush=True)
