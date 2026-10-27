# encaje: frontera en alpha de la desigualdad de Zieliński–Zych (QSL.zz_inequality, probada en Lean para 0<alpha<=1):
# ¿se mantiene para alpha > 1? investigación (falsar antes de plantear), no herramienta.
"""f_alpha(x) = x^alpha - pi^alpha/2 + (pi^alpha/2) cos x + alpha pi^(alpha-1) sin x >= 0 for x >= 0.
Scan alpha on a grid; for each, the minimum of f over x in [0, 60] (fine grid + local refinement with mpmath).
Controls: alpha = 1 and alpha = 0.5 must give min >= 0 (proved); a deliberately wrong function (drop the sin term)
must go negative."""
import numpy as np
from mpmath import mp, mpf, cos, findroot, pi, sin

mp.dps = 40


def f(alpha, x):
    return x ** alpha - pi ** alpha / 2 + (pi ** alpha / 2) * cos(x) + alpha * pi ** (alpha - 1) * sin(x)


def minimo(alpha, g=f, xmax=60.0):
    xs = np.linspace(1e-9, xmax, 120001)
    a = float(alpha)
    vals = xs ** a - np.pi ** a / 2 + (np.pi ** a / 2) * np.cos(xs) + a * np.pi ** (a - 1) * np.sin(xs) \
        if g is f else np.array([float(g(mpf(alpha), mpf(x))) for x in xs[::200]])
    if g is not f:
        return float(vals.min()), None
    i = int(vals.argmin())
    x0 = xs[i]
    try:   # refine at the stationary point
        xr = findroot(lambda x: (g(mpf(alpha), x + mpf('1e-12')) - g(mpf(alpha), x - mpf('1e-12'))) / mpf('2e-12'),
                      mpf(x0))
        m = g(mpf(alpha), xr)
        return float(min(m, mpf(vals[i]))), float(xr)
    except Exception:
        return float(vals[i]), float(x0)


def sin_seno(alpha, x):
    return x ** alpha - pi ** alpha / 2 + (pi ** alpha / 2) * cos(x)


print('control + alpha=1  :', minimo(1.0))
print('control + alpha=0.5:', minimo(0.5))
print('control - sin seno, alpha=1:', minimo(1.0, g=sin_seno)[0], '(debe ser < 0)')
print()
print(' alpha    min f        argmin x')
for alpha in [1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.7, 1.8, 1.9, 2.0, 2.2, 2.5, 3.0]:
    m, x = minimo(alpha)
    print(f'{alpha:5.2f}  {m: .3e}   {x}')
