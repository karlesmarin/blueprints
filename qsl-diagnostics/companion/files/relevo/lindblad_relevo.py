"""Simulación Lindblad del relevo cúbit A → modo C → cúbit B (réplica independiente del modelo de error de IBM).
# encaje: módulo de la misión relevo (qsl-hardware); numpy/scipy propio (no hay qutip instalado ni pieza de Excovery
# que simule canales abiertos); el modelo de IBM es de «tiempo en cada elemento», esto resuelve la dinámica entera.

Espacio: {|0⟩ vacío, |A⟩, |C⟩, |B⟩}. H(t) = g1(t)(|A⟩⟨C| + h.c.) + g2(t)(|C⟩⟨B| + h.c.), a trozos constante.
Disipación por elemento j: relajación √(1/T1_j)|0⟩⟨j| y desfase puro √(2γφ_j)|j⟩⟨j| con γφ = 1/T2 − 1/(2T1).
Fidelidad media del canal cúbit (|0⟩,|A⟩) → (|0⟩,|B⟩) con la fase de |B⟩ corregida (Z local): media sobre los
6 estados ±x, ±y, ±z (2-diseño: media de estados = fidelidad media de la puerta).
"""
import argparse
import math
import numpy as np
from scipy.linalg import expm

D = 4
V, A, C, B = range(4)


def ket(i):
    v = np.zeros(D, complex); v[i] = 1; return v


def liouvilliano(H, Ls):
    I = np.eye(D)
    Lv = -1j * (np.kron(I, H) - np.kron(H.T, I))          # vec por columnas: vec(XρY) = (Yᵀ ⊗ X) vec ρ
    for L in Ls:
        LdL = L.conj().T @ L
        Lv += np.kron(L.conj(), L) - 0.5 * np.kron(I, LdL) - 0.5 * np.kron(LdL.T, I)
    return Lv


def disipadores(T1, T2, desfase_mal=False):
    """T1, T2: dict elemento -> µs; claves 'q' (los dos cúbits) o 'a', 'b' (cada uno), y 'c' (modo).
    Tiempos de la simulación en µs."""
    Ls = []
    par = lambda d, k: d.get(k, d.get('q'))
    for j, (t1, t2) in ((A, (par(T1, 'a'), par(T2, 'a'))), (C, (T1['c'], T2['c'])), (B, (par(T1, 'b'), par(T2, 'b')))):
        P = np.outer(ket(j), ket(j))
        Ls.append(math.sqrt(1 / t1) * np.outer(ket(V), ket(j)))
        gphi = (1 / t2) if desfase_mal else (1 / t2 - 1 / (2 * t1))
        Ls.append(math.sqrt(2 * gphi) * P)
    return Ls


def evolucionar(rho, tramos, Ls):
    """tramos: lista de (dt µs, g1, g2) con g en rad/µs."""
    v = rho.reshape(-1, order='F')
    for dt, g1, g2 in tramos:
        H = np.zeros((D, D), complex)
        H[A, C], H[C, A] = g1, np.conj(g1)
        H[C, B], H[B, C] = g2, np.conj(g2)
        v = expm(liouvilliano(H, Ls) * dt) @ v
    return v.reshape(D, D, order='F')


def fidelidad_media(tramos, Ls, origen=A, destino=B):
    """Fase relativa de |destino⟩ corregida con la evolución cerrada (Z local: no cuesta tiempo)."""
    # fase de la amplitud en |destino⟩ desde la evolución unitaria de |origen⟩
    U = np.eye(D, dtype=complex)
    for dt, g1, g2 in tramos:
        H = np.zeros((D, D), complex)
        H[A, C], H[C, A] = g1, np.conj(g1); H[C, B], H[B, C] = g2, np.conj(g2)
        U = expm(-1j * H * dt) @ U
    fase = np.angle(U[destino, origen]) if abs(U[destino, origen]) > 1e-9 else 0.0
    estados = []
    for a, b in ((1, 0), (0, 1), (1, 1), (1, -1), (1, 1j), (1, -1j)):
        n = math.sqrt(abs(a) ** 2 + abs(b) ** 2)
        estados.append((a / n, b / n))
    F = 0.0
    for a, b in estados:
        psi = a * ket(V) + b * ket(origen)
        rho = evolucionar(np.outer(psi, psi.conj()), tramos, Ls)
        obj = a * ket(V) + b * np.exp(1j * fase) * ket(destino)
        F += float(np.real(obj.conj() @ rho @ obj))
    return F / 6


def ec1(t, T1, T2):
    """IBM ec. (1): error de un elemento que retiene la excitación un tiempo t."""
    return 0.5 * (1 - (math.exp(-t / T1) + 2 * math.exp(-t / T2)) / 3)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('modo', choices=['control_estatico', 'cerrado', 'optimo'])
    ap.add_argument('--T1q', type=float, default=121.0); ap.add_argument('--T2q', type=float, default=14.0)
    ap.add_argument('--T1c', type=float, default=28.8); ap.add_argument('--T2c', type=float, default=36.0)
    ap.add_argument('--g', type=float, default=9.0, help='g/2π en MHz')
    ap.add_argument('--desfase_mal', action='store_true', help='control negativo: γφ = 1/T2 (falta −1/2T1)')
    ap.add_argument('--trozos', type=int, default=1)
    a = ap.parse_args()
    T1 = dict(q=a.T1q, c=a.T1c); T2 = dict(q=a.T2q, c=a.T2c)
    Ls = disipadores(T1, T2, a.desfase_mal)
    g = 2 * math.pi * a.g                                   # rad/µs
    if a.modo == 'control_estatico':
        t = 0.156                                           # µs: la excitación quieta en A, sin acoplamiento
        F = fidelidad_media([(t, 0, 0)], Ls, origen=A, destino=A)
        print(f'estatico: simulado = {100 * (1 - F):.6f} %, ec1 = {100 * ec1(t, a.T1q, a.T2q):.6f} %')
        print(f'error estatico = {100 * (1 - F):.6f}')
    elif a.modo == 'cerrado':
        T = math.pi / (math.sqrt(2) * g)
        F = fidelidad_media([(T / a.trozos, g, g)] * a.trozos, [], origen=A, destino=B)
        print(f'fidelidad cerrada al optimo = {F:.9f}')
    else:
        T = math.pi / (math.sqrt(2) * g)
        F = fidelidad_media([(T / a.trozos, g, g)] * a.trozos, Ls, origen=A, destino=B)
        print(f'T_min = {1000 * T:.2f} ns; error Lindblad al optimo = {100 * (1 - F):.4f} %')


if __name__ == '__main__':
    main()
