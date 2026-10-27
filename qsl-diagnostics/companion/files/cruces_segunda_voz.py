# encaje: verificación PROPIA de los cruces propuestos por la segunda voz (27-oct): (1) residuo 1/(1-e^-2) y área
# reconstruida por qubit; (2) CZ con qutrits en pi/(6g) por promedio local + código en autovectores extremos de Q;
# (3) tabla lambda_d, kappa_d y cociente de cotas. Investigación, no herramienta; no ejecuta su código.
import json
from pathlib import Path

import numpy as np
from scipy.linalg import expm

AQUI = Path(__file__).parent
print('(1) 1/(1-e^-2) =', 1 / (1 - np.exp(-2)))


def areas(N, s):
    c = N / 2
    g = lambda x: np.exp(-((x - c) ** 2) / (2 * s ** 2))
    S = sum(g(n + 0.5) for n in range(N))
    return S - N * g(-0.5), (S - N * g(-1)) / (1 - g(-1))      # A_rec, A_Q (units of dt)


for s in (24, 40, 80, 640):
    ar, aq = areas(4 * s, s)
    print(f'    sigma {s}: A_Q/A_rec = {aq / ar:.10f}')
errs, n = [], 0
for b in sorted(d for d in (AQUI / 'datos_pulsos').iterdir() if d.is_dir()):
    d = json.loads((b / f'defs_{b.name}.json').read_text())
    c = json.loads((b / f'conf_{b.name}.json').read_text())
    v = (c.get('hamiltonian') or {}).get('vars', {})
    dt = c['dt'] * (1e9 if c['dt'] < 1e-6 else 1)
    for cmd in d.get('cmd_def', []):
        if cmd['name'] != 'x' or len(cmd['qubits']) != 1:
            continue
        q = cmd['qubits'][0]
        pp = [s for s in cmd['sequence'] if s.get('name') == 'parametric_pulse']
        if not pp or f'omegad{q}' not in v:
            continue
        p = pp[0]['parameters']
        a = p['amp']
        amp = abs(complex(*a)) if isinstance(a, list) else abs(a)
        ar, _ = areas(int(p['duration']), float(p['sigma']))
        errs.append(v[f'omegad{q}'] * amp * ar * dt / np.pi - 1)
print(f'    omegad*amp*A_rec/pi - 1 over {len(errs)} qubits: max |.| = {np.max(np.abs(errs)):.2e}, '
      f'median {np.median(errs):.2e}')

# (2) CZ construction, d = 3, g = 1
d = 3
a = np.diag(np.sqrt(np.arange(1, d)), 1)
Q, P = a + a.T, 1j * (a.T - a)
Hc = np.kron(a.T, a) + np.kron(a, a.T)
print('(2) Hc == (QQ+PP)/2:', np.allclose(Hc, (np.kron(Q, Q) + np.kron(P, P)) / 2))
ev, V = np.linalg.eigh(Q)
W = V @ np.diag(np.exp(2j * np.pi * np.arange(d) / d)) @ V.conj().T
Hav = sum(np.kron(np.linalg.matrix_power(W, k), np.eye(d)) @ Hc @ np.kron(np.linalg.matrix_power(W, -k), np.eye(d))
          for k in range(d)) / d
print('    twirl == QQ/2:', np.allclose(Hav, np.kron(Q, Q) / 2), '; eigenvalues of Q:', np.round(ev, 4))
xm, xp = V[:, 0], V[:, -1]
code = np.stack([np.kron(u, w) for u in (xp, xm) for w in (xp, xm)], axis=1)     # |++>,|+->,|-+>,|-->
T = np.pi / 6
Ul = code.conj().T @ expm(-1j * T * Hav) @ code
ph = np.angle(np.diag(Ul) / Ul[0, 0])
print(f'    logical block at T = pi/6: unitary {np.allclose(Ul @ Ul.conj().T, np.eye(4))}, relative phases/pi =',
      np.round(ph / np.pi, 6), '(ZZ-type: CZ up to local Z iff phases ~ (0, a, b, a+b+-1))')
print('    p2 of extreme eigenvectors:', np.round(abs(xp[2]) ** 2, 6), np.round(abs(xm[2]) ** 2, 6),
      '; outside-qubit population of a code state:', np.round(1 - (1 - abs(xp[2]) ** 2) ** 2, 6))

# (3) lambda_d, kappa_d
print('(3)  d   lower=pi/(4 kappa)  upper=pi/(2 lambda^2)  ratio')
for d in (2, 3, 4, 5, 10, 20):
    a = np.diag(np.sqrt(np.arange(1, d)), 1)
    lam = np.linalg.eigvalsh(a + a.T)[-1]
    kap = np.linalg.norm(np.kron(a.T, a) + np.kron(a, a.T), 2)
    lo, up = np.pi / (4 * kap), np.pi / (2 * lam ** 2)
    print(f'    {d:3d}   {lo:.6f}            {up:.6f}             {up / lo:.4f}')
