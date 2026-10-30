"""Depuración: misma dinámica, dos códigos (superoperador frente a RK4) y dos estimadores de fidelidad.
# encaje: control de investigación (qsl-hardware, relevo).
"""
import math
import numpy as np
import lindblad_relevo as S
import lindblad_rk4 as R

g = 2 * math.pi * 9.0
T = math.pi / (math.sqrt(2) * g)
T1 = dict(q=1e9, c=1e9); T2 = dict(q=14.0, c=2e9)          # solo desfase de cúbits
Ls = S.disipadores(T1, T2)
H = np.zeros((4, 4), complex); H[1, 2] = H[2, 1] = H[2, 3] = H[3, 2] = g
g1T1 = {1: 1e-9, 2: 1e-9, 3: 1e-9}; gphi = {1: 1 / 14.0, 2: 0.0, 3: 1 / 14.0}
for i, k in ((0, 1), (1, 1), (1, 0)):
    rho = np.zeros((4, 4), complex); rho[i, k] = 1
    a = S.evolucionar(rho, [(T, g, g)], Ls)
    b = R.evolucion(rho, H, g1T1, gphi, T, 4000)
    print(i, k, 'superop', np.round(a[[0, 3]][:, [0, 3]], 6).tolist(), ' rk4', np.round(b[[0, 3]][:, [0, 3]], 6).tolist())
print('6 estados:', 100 * (1 - S.fidelidad_media([(T, g, g)], Ls, S.A, S.B)))
