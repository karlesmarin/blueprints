# encaje: control de MONOTONÍA de grape_cr.py (revisión externa 27-oct): una solución factible con tope r1 debe seguir
# siéndolo con r2 > r1 (mismo pulso, misma fidelidad); y continuación en amplitud; investigación, no herramienta.
"""1) Find a CNOT at T = f * pi/(2J) with cap r1 (best of several starts). 2) Re-express the SAME pulse under cap r2 > r1:
amplitude r1 tanh(x) = r2 tanh(x') with x' = atanh(r1/r2 tanh x); its error must be identical (code consistency).
3) Continuation: from that seed, optimize at shorter times with cap r2 and report the shortest feasible time found.
Usage: python grape_cr_continuacion.py r1 r2,r3 f1,f2,... (f = T in units of pi/(2J); f1 is where r1 is solved)"""
import sys

import numpy as np
from scipy.optimize import minimize

import grape_cr as g

r1 = float(sys.argv[1])
r2s = [float(x) for x in sys.argv[2].split(',')]
fs = [float(x) for x in sys.argv[3].split(',')]
T0 = fs[0] * np.pi / (2 * g.J)
x1, e1 = None, 1.0
for _ in range(8):
    x0 = np.concatenate([g.rng.normal(size=g.M) + 2, g.rng.uniform(0, 6.3, g.M), g.rng.normal(size=g.M) * 0.5,
                         g.rng.uniform(0, 6.3, g.M), g.rng.normal(size=12)])
    res = minimize(g.infid, x0, args=(T0, r1), method='L-BFGS-B', options=dict(maxiter=2500))
    if res.fun < e1:
        x1, e1 = res.x, res.fun
    if e1 < 1e-4:
        break
print(f'r1 = {r1}: T = {fs[0]:.2f} pi/(2J) -> 1-F = {e1:.2e}', flush=True)
for r2 in r2s:
    x2 = x1.copy()
    x2[:g.M] = np.arctanh(r1 / r2 * np.tanh(x1[:g.M]))
    print(f'  same pulse under cap r2 = {r2}: 1-F = {g.infid(x2, T0, r2):.2e} (must equal {e1:.2e})', flush=True)
    xs = x2
    for f in fs[1:]:
        T = f * np.pi / (2 * g.J)
        res = minimize(g.infid, xs, args=(T, r2), method='L-BFGS-B', options=dict(maxiter=4000))
        print(f'    continuation r2 = {r2}: T = {f:.2f} pi/(2J) -> 1-F = {res.fun:.2e}', flush=True)
        if res.fun < 1e-3:
            xs = res.x
