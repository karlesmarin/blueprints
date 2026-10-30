"""Réplica independiente de lindblad_relevo.py: ecuación maestra integrada con RK4 sobre ρ (sin superoperador ni
expm), desfase escrito como decaimiento de coherencias y fidelidad media por la fórmula de Nielsen con la matriz de
proceso en la base de Pauli del cúbit lógico (no por los 6 estados).
# encaje: réplica de la misión relevo (qsl-hardware); código aparte a propósito: no importa lindblad_relevo.

Uso: python lindblad_rk4.py --T1q 121.0 --T2q 14.0 --T1c 28.8 --T2c 36.0 --g 9.0
"""
import argparse
import math
import numpy as np


def derivada(rho, H, g1T1, gphi):
    """dρ/dt. g1T1[j] = 1/T1_j (relajación j → vacío 0), gphi[j] = γφ_j (desfase puro de j)."""
    d = -1j * (H @ rho - rho @ H)
    n = rho.shape[0]
    for j in (1, 2, 3):
        k = g1T1[j]
        d[0, 0] += k * rho[j, j]
        for a in range(n):                                 # −½k{|j⟩⟨j|, ρ}
            if a != j:
                d[j, a] -= 0.5 * k * rho[j, a]
                d[a, j] -= 0.5 * k * rho[a, j]
        d[j, j] -= k * rho[j, j]
        for a in range(n):                                 # desfase: coherencias ρ_ja (a ≠ j) decaen a 2γφ·½·2 = 2γφ? no:
            if a != j:                                     # L = √(2γφ)|j⟩⟨j| ⇒ dρ_ja/dt = −γφ ρ_ja
                d[j, a] -= gphi[j] * rho[j, a]
                d[a, j] -= gphi[j] * rho[a, j]
    return d


def evolucion(rho, H, g1T1, gphi, T, pasos):
    h = T / pasos
    for _ in range(pasos):
        k1 = derivada(rho, H, g1T1, gphi)
        k2 = derivada(rho + 0.5 * h * k1, H, g1T1, gphi)
        k3 = derivada(rho + 0.5 * h * k2, H, g1T1, gphi)
        k4 = derivada(rho + h * k3, H, g1T1, gphi)
        rho = rho + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return rho


def main():
    ap = argparse.ArgumentParser()
    for n, v in (('T1q', 121.0), ('T2q', 14.0), ('T1c', 28.8), ('T2c', 36.0), ('g', 9.0)):
        ap.add_argument('--' + n, type=float, default=v)
    ap.add_argument('--pasos', type=int, default=4000)
    a = ap.parse_args()
    g = 2 * math.pi * a.g
    T = math.pi / (math.sqrt(2) * g)
    H = np.zeros((4, 4), complex)
    H[1, 2] = H[2, 1] = H[2, 3] = H[3, 2] = g               # 0 vacío, 1 A, 2 C, 3 B
    T1 = {1: a.T1q, 2: a.T1c, 3: a.T1q}; T2 = {1: a.T2q, 2: a.T2c, 3: a.T2q}
    g1T1 = {j: 1 / T1[j] for j in T1}
    # L = √(2γφ)|j⟩⟨j| da dρ_ja/dt = −½·2γφ ρ_ja = −γφ ρ_ja, con γφ = 1/T2 − 1/(2T1)
    gphi = {j: 1 / T2[j] - 1 / (2 * T1[j]) for j in T1}
    # canal lógico: base {|0⟩, |1⟩} → entrada {vacío, A}, salida {vacío, B} con la fase −1 de B corregida
    Ein = {(0, 0): (0, 0), (0, 1): (0, 1), (1, 0): (1, 0), (1, 1): (1, 1)}
    salida = {}
    for (i, k), _ in Ein.items():
        rho = np.zeros((4, 4), complex)
        rho[0 if i == 0 else 1, 0 if k == 0 else 1] = 1    # |i⟩⟨k| lógico
        r = evolucion(rho, H, g1T1, gphi, T, a.pasos)
        idx = [0, 3]
        salida[(i, k)] = np.array([[r[idx[x], idx[y]] for y in range(2)] for x in range(2)])
    Zc = np.diag([1, -1])                                   # corrige la fase −1 de |B⟩ (U_BA = −1 al óptimo)
    # fidelidad de entrelazamiento: F_e = ⟨Φ|(1⊗E)(Φ)|Φ⟩ = (1/4) Σ_{ik} ⟨i|E'(|i⟩⟨k|)|k⟩
    Fe = sum(np.real((Zc @ salida[(i, k)] @ Zc)[i, k]) for i in (0, 1) for k in (0, 1)) / 4
    # el canal NO conserva la traza en {vacío, B}: con desfase parte de la excitación se queda en A o C (fuga).
    # Fidelidad media de un mapa CP general: (d·F_e + Tr E(1)/d)/(d + 1); (2F_e + 1)/3 solo vale si Tr E(1) = d
    # (depurar_replica.py, 30-oct: la fórmula sin fuga daba 0,089 % frente a 0,108 % de los 6 estados)
    TrE1 = np.real(np.trace(salida[(0, 0)]) + np.trace(salida[(1, 1)]))
    Fm = (2 * Fe + TrE1 / 2) / 3
    print(f'error RK4 al optimo = {100 * (1 - Fm):.4f} %')


if __name__ == '__main__':
    main()
