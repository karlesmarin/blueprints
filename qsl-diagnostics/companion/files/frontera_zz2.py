# encaje: barrido fino de la frontera en alpha de la desigualdad de Zieliński–Zych (sigue a frontera_zz.py); investigación.
"""Minimum of f_alpha on (0, X] EXCLUDING neighbourhoods of the trivial zeros x = 0 and x = pi, divided by the scale
pi^alpha, for alpha on a fine grid in (0, 10]. Negative = the inequality fails for that alpha."""
import numpy as np

xs = np.linspace(1e-6, 200.0, 2_000_001)
lejos = (np.abs(xs - np.pi) > 1e-3) & (xs > 1e-3)
peor = []
for alpha in np.concatenate([np.linspace(0.05, 1.0, 20), np.linspace(1.0, 2.0, 41), np.linspace(2.0, 10.0, 33)]):
    a = float(alpha)
    f = xs ** a - np.pi ** a / 2 + (np.pi ** a / 2) * np.cos(xs) + a * np.pi ** (a - 1) * np.sin(xs)
    g = f[lejos] / np.pi ** a
    i = int(g.argmin())
    peor.append((a, float(g[i]), float(xs[lejos][i])))
neg = [p for p in peor if p[1] < 0]
print('alphas probados:', len(peor), '· con mínimo negativo:', len(neg))
for p in peor[::6] + neg[:10]:
    print(f'alpha={p[0]:.3f}  min f/pi^a = {p[1]: .4e}  en x = {p[2]:.4f}')
