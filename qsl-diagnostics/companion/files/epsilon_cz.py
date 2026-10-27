# encaje: infidelidad de ESTADO de la CZ numérica para la entrada |++> (la que usa la cota de entrelazamiento) y la cota
# robusta correspondiente (pi/4 - arcsin sqrt eps)/(2J) (Lean ApproxSpeedLimits); investigación, no herramienta.
"""For a saved solution of grape_cz_torch.py: psi_out = U |++> (qubit-subspace input), target CZ|++> = (|0+> + |1->)/sqrt2.
eps = 1 - |<target|psi_out>|^2 (leakage included: psi_out keeps its components outside the qubit subspace).
Lower bound on the time for the SAME tolerance: T >= (pi/4 - arcsin sqrt eps) / ||Hc||, ||Hc|| = 2J for d = 3.
Usage: python epsilon_cz.py cz_best_d3_M8_T0.5500_a10.0.npy [...]"""
import re
import sys

import numpy as np
from scipy.linalg import expm

from verificar_cz import acotar, herm

for f in sys.argv[1:]:
    m = re.search(r'd(\d+)_M(\d+)_T([\d.]+)_a([\w.]+)\.npy', f)
    d, M, T = int(m[1]), int(m[2]), float(m[3])
    amax = None if m[4] == 'None' else float(m[4])
    x = np.load(f)
    n = d * d
    b = np.diag(np.sqrt(np.arange(1, d)), 1)
    Hc = np.kron(b.T, b) + np.kron(b, b.T)
    U = np.kron(expm(1j * herm(x[0:n], d)), expm(1j * herm(x[n:2 * n], d)))
    q = 4 * n
    for _ in range(M):
        A, B = acotar(herm(x[q:q + n], d), amax), acotar(herm(x[q + n:q + 2 * n], d), amax)
        U = expm(-1j * (T / M) * (np.kron(A, np.eye(d)) + np.kron(np.eye(d), B) + Hc)) @ U
        q += 2 * n
    U = np.kron(expm(1j * herm(x[2 * n:3 * n], d)), expm(1j * herm(x[3 * n:4 * n], d))) @ U
    e = np.zeros(d)
    plus = e.copy()
    plus[:2] = 1 / np.sqrt(2)
    psi = U @ np.kron(plus, plus)
    tgt = np.zeros(n, complex)
    for i in range(2):
        for j in range(2):
            tgt[i * d + j] = 0.5 * (-1 if (i, j) == (1, 1) else 1)
    eps = 1 - abs(np.vdot(tgt, psi)) ** 2
    cota = (np.pi / 4 - np.arcsin(np.sqrt(max(eps, 0)))) / 2
    print(f'{f}: eps(|++>) = {eps:.2e}; robust lower bound (pi/4 - arcsin sqrt eps)/(2J) = {cota:.5f}/J '
          f'(exact-task bound {np.pi / 8:.5f}/J); found T = {T}/J')
