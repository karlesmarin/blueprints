# encaje: script autónomo del companion (versión 3 de qsl-diagnostics): comprueba en doble precisión el revival de la
# construcción por el bloque {ll, mm, hh} (numpy/scipy, sin Excovery). Misma cuenta que paper_cz/v213/b1.
"""Version 3, upper bound (idealised): the average of 18 local conjugates of H_c plus a local detuning of |m> gives an
exact CZ up to local phases at T2 = 3*pi/(2*(1+sqrt(65))*J).  Units J = 1.  Prints leakage, off-diagonal norm and the
entangling phase (pi for a CZ).  The finite-time protocol and its interval certificate are reported in
cz_v3_certificado_salida.txt (the interval tools are not part of this package)."""
import numpy as np
from scipy.linalg import expm

s2, s3, s6 = np.sqrt(2), np.sqrt(3), np.sqrt(6)
V = np.array([[1 / s6, s2 / s3, 1 / s6], [-s3 / s6, 0, s3 / s6], [s2 / s6, -1 / s3, s2 / s6]])   # eigenbasis of b+b†
b = np.diag([1.0, s2], 1)
Q = V.T @ (b + b.T) @ V
Pi = V.T @ (1j * (b.T - b)) @ V
h0 = 0.5 * (np.kron(Q, Q) + np.kron(Pi, Pi))          # H_c / J = b⊗b† + b†⊗b
assert np.allclose(np.diag(Q), [-s3, 0, s3])
w = np.exp(2j * np.pi / 3)
s = 2 * np.sqrt(65) - 16
r = np.sqrt((1 + s) / 2)
th = np.arccos(r)
H = np.zeros((9, 9), complex)
for sg in (1, -1):
    R = np.kron(np.diag([np.exp(1j * sg * th), 1, np.exp(-1j * sg * th)]), np.eye(3))
    for p in range(3):
        for q in range(3):
            D = np.diag([1, w ** p, w ** q])
            G = R @ np.kron(D, D.conj())
            H += G @ h0 @ G.conj().T / 18                # convex combination: interaction cost one per unit time
a, c = 1.5, s / 6
d = a - c - 12
Pm = np.diag([0, 1, 0.0])
H += d / 2 * (np.kron(Pm, np.eye(3)) + np.kron(np.eye(3), Pm))   # local detuning: no interaction cost
T2 = 3 * np.pi / (2 * (1 + np.sqrt(65)))
code = [0, 2, 6, 8]                                        # ll, lh, hl, hh
U = expm(-1j * H * T2)[np.ix_(code, code)]
dg = np.diag(U)
print(f'T2 = {T2:.13f}/J   (pi/6 = {np.pi / 6:.13f})')
print(f'identity s^2 + 32 s - 4 = {s * s + 32 * s - 4:.2e}')
print(f'leakage {np.linalg.norm(np.eye(4) - U.conj().T @ U):.2e}, off-diagonal {np.linalg.norm(U - np.diag(dg)):.2e}')
print(f'entangling phase {np.angle(dg[0] * dg[3] / (dg[1] * dg[2])):.12f}  (CZ: pi = {np.pi:.12f})')
