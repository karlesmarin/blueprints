# Proposition 6.3: the two deficit identities, symbolically (SymPy).
import itertools
from fractions import Fraction

import sympy as sp

x, y, z = sp.symbols('x y z', positive=True)
n = x + y + z
s = y + z
u = x + y - 2
M1 = (s - 1) * ((x - 1) * s + y * z) / (s * (n - 2))
M2 = (u + 1) * (z * u + (x - 1) * (y - 1)) / (u * (n - 1))
# identidades de déficit
eta1 = x - (y + z) / 2
d1 = eta1 * (2 * eta1 - 1) / (6 * (n - 2)) + (s - 1) * (y - z) ** 2 / (4 * s * (n - 2))
eta2 = (x + y) / 2 - z
d2 = eta2 * (2 * eta2 - 1) / (6 * (n - 1)) + (u + 1) * (x - y) ** 2 / (4 * u * (n - 1))
print('identidad de déficit I :', sp.simplify(n / 3 - sp.Rational(1, 2) - M1 - d1) == 0)
print('identidad de déficit II:', sp.simplify(n / 3 - sp.Rational(1, 2) - M2 - d2) == 0)
# nuestros módulos
B, c = sp.symbols('B c', positive=True)
mod1 = (2 * c - 1) * (2 * B + c - 2) / (2 * (2 * c + B - 2))
mod2 = (2 * B - 1) * (B + 2 * c - 1) / (2 * (2 * B + c - 1))
print('M1(B,c,c) = módulo (B,c,c):', sp.simplify(M1.subs({x: B, y: c, z: c}) - mod1) == 0)
print('M2(B,B,c) = módulo (B,B,c):', sp.simplify(M2.subs({x: B, y: B, z: c}) - mod2) == 0)


def lam(N):
    r = N % 3
    return Fraction(2 * N - 3, 6) if r == 0 else (Fraction((N - 1) * (2 * N - 5), 6 * (N - 2)) if r == 1
                                                  else Fraction((N - 2) * (2 * N - 1), 6 * (N - 1)))


def M(a, b, cc):
    a, b, cc = sorted((a, b, cc), reverse=True)
    if cc * (a - 1) >= b * (b - 1):
        S = b + cc
        return Fraction((S - 1) * ((a - 1) * S + b * cc), S * (a + b + cc - 2))
    U = a + b - 2
    return Fraction((U + 1) * (cc * U + (a - 1) * (b - 1)), U * (a + b + cc - 1))


malos = []
for N in range(3, 61):
    vals = {(a, b, N - a - b): M(a, b, N - a - b) for a in range(1, N) for b in range(1, N - a)}
    mx = max(vals.values())
    arg = {tuple(sorted(k)) for k, v in vals.items() if v == mx}
    equil = all(max(t) - min(t) <= 1 for t in arg)
    if mx != lam(N) or not equil:
        malos.append((N, mx, lam(N), arg))
print('n = 3..60: máximo de M sobre x+y+z = n igual a λ_n y alcanzado solo en equilibrados:', not malos, malos[:3])
# frontera: z(x-1) = y(y-1) -> M1 = M2 (comprobación numérica en las soluciones enteras pequeñas)
fr = [(a, b, cc) for a in range(1, 40) for b in range(1, a + 1) for cc in range(1, b + 1) if cc * (a - 1) == b * (b - 1) and a + b > 2]
ok = all(Fraction((b + cc - 1) * ((a - 1) * (b + cc) + b * cc), (b + cc) * (a + b + cc - 2)) ==
         Fraction((a + b - 1) * (cc * (a + b - 2) + (a - 1) * (b - 1)), (a + b - 2) * (a + b + cc - 1)) for a, b, cc in fr)
print('frontera: M1 = M2 en', len(fr), 'ternas enteras:', ok)
# identidades contables
m_, nn, b_, t_ = sp.symbols('m n b t')
e = b_ + 2 * t_
Q = b_ + t_
h = m_ * nn - e
zz, d = sp.symbols('z d')
print('Q = (e+b)/2:', sp.simplify(Q - (e + b_) / 2) == 0, '; 2Q = mn + z - h - d con b = z - d:',
      sp.simplify((2 * Q - (m_ * nn + zz - h - d)).subs(b_, zz - d)) == 0)
