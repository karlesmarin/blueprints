"""evlib.py -- evaluador PROPIO de caracteres de Sp(2m) (comprobaciones independientes de aP_alco.tex).
QUE: tres instrumentos distintos, sin importar nada del paper ni de los otros programas:
  (PS)  chi_lambda(g_theta) = z^{-(lam,rho)} prod_{a>0} (1-z^{(l,a)})/(1-z^{(rho,a)}), z=e^{2 pi i theta}:
        se calcula el POLINOMIO entero Q(z) (division exacta), se reduce mod z^q-1 (anillo de grupo
        exacto Z[C_q]) y mod Phi_q (exacto: decide si el valor es racional y cual). No usa limites.
  (JT)  Koike-Terada sp_lambda = 1/2 det(h_{l_i-i+j} + h_{l_i-i-j+2}) desde el ESPECTRO (multiconjunto de
        raices de la unidad); h_r exactos en Z[C_N], determinante numerico mpmath a 150 digitos.
  (WD)  determinantes de Weyl en un punto regular generico (control de JT).
  Dimensiones GL/Sp/SO(2n+1) por la formula de Weyl con Fraction.
POR QUE: los Teoremas C y D se comprueban con un instrumento que no importa nada de los otros programas.
"""
import itertools
from fractions import Fraction
from functools import lru_cache
import numpy as np
import mpmath as mp
import sympy

mp.mp.dps = 60


def rho(m):
    return list(range(m, 0, -1))


def root_vals(x):
    """valores (x,alpha), alpha>0 en C_m, forma con (e_i,e_j)=delta (raices cortas de norma 2)."""
    m = len(x); v = []
    for i in range(m):
        for j in range(i + 1, m):
            v.append(x[i] - x[j]); v.append(x[i] + x[j])
        v.append(2 * x[i])
    return v


def coroot_vals(x):
    m = len(x); v = []
    for i in range(m):
        for j in range(i + 1, m):
            v.append(x[i] - x[j]); v.append(x[i] + x[j])
        v.append(x[i])
    return v


def dominantes(m, L):
    for lam in itertools.combinations_with_replacement(range(L, -1, -1), m):
        yield list(lam)


# ---------------- (PS) polinomio exacto ----------------
def ps_poly(lam):
    """devuelve (Q, s): Q array object con coef. de Q(z)=prod(1-z^A)/prod(1-z^B), s=(lam,rho)."""
    m = len(lam); r = rho(m); l = [lam[i] + r[i] for i in range(m)]
    A = root_vals(l); B = root_vals(r)
    deg = sum(A)
    P = np.zeros(deg + 1, dtype=object); P[:] = 0; P[0] = 1
    for a in A:
        P[a:] = P[a:] - P[:-a].copy() if a <= deg else P[a:]
    for b in B:
        # P = (1-z^b) Q  ->  Q[n] = P[n] + Q[n-b]: cumsum por bloques de tamano b
        n = len(P); pad = (-n) % b
        R = np.concatenate([P, np.zeros(pad, dtype=object)]); R[n:] = 0
        R = R.reshape(-1, b).cumsum(axis=0).reshape(-1)
        Q = R[:n]
        # comprobar division exacta: grado real
        P = Q
    # el cociente debe ser polinomio de grado sum(A)-sum(B): coeficientes por encima han de ser 0
    dQ = sum(A) - sum(B)
    assert all(c == 0 for c in P[dQ + 1:]), "division no exacta"
    s = sum(lam[i] * r[i] for i in range(m))
    assert dQ == 2 * s
    return P[:dQ + 1], s


def fold(Q, s, q):
    """chi como elemento de Z[C_q]: v[k] = coef de zeta^k."""
    v = [0] * q
    for n, c in enumerate(Q):
        if c:
            v[(n - s) % q] += int(c)
    return v


@lru_cache(None)
def cyclo(q):
    x = sympy.Symbol('x')
    return [int(c) for c in sympy.Poly(sympy.cyclotomic_poly(q, x), x).all_coeffs()[::-1]]  # bajo->alto


def mod_cyclo(v, q):
    """reduce el polinomio sum v[k] x^k modulo Phi_q (monico). Devuelve lista de coef (grado<phi)."""
    c = cyclo(q); d = len(c) - 1
    r = list(v)
    for k in range(len(r) - 1, d - 1, -1):
        t = r[k]
        if t:
            for i in range(d + 1):
                r[k - d + i] -= t * c[i]
    return r[:d] if d > 0 else []


def rational_value(v, q):
    """si el elemento de Z[zeta_q] es entero racional devuelve ese entero, si no None."""
    if q == 1:
        return sum(v)
    r = mod_cyclo(v, q)
    if all(x == 0 for x in r[1:]):
        return r[0]
    return None


def eval_gr(v, q, p=1):
    return mp.fsum(c * mp.expjpi(mp.mpf(2) * ((p * k) % q) / q) for k, c in enumerate(v) if c)


def chi_ps(lam, p, q, cache={}):
    key = tuple(lam)
    if key not in cache:
        cache[key] = ps_poly(lam)
    Q, s = cache[key]
    return fold(Q, s, q)


# ---------------- (JT) Koike-Terada desde el espectro ----------------
def h_gr(exps, N, K):
    h = [[0] * N for _ in range(K + 1)]
    h[0][0] = 1
    for e in exps:
        for k in range(1, K + 1):
            prev = h[k - 1]; cur = h[k]
            for i, x in enumerate(prev):
                if x:
                    cur[(i + e) % N] += x
    return h


def chi_jt_spectrum(lam, exps, N):
    """chi_lambda en el elemento de espectro {zeta_N^e : e in exps} (2m letras). Numerico, 150 digitos."""
    old = mp.mp.dps; mp.mp.dps = 150
    lamp = [x for x in lam if x > 0]; n = len(lamp)
    if n == 0:
        mp.mp.dps = old; return mp.mpc(1)
    K = lamp[0] + n + 2
    h = h_gr(exps, N, K)
    hv = [eval_gr(hk, N) for hk in h]
    H = lambda k: hv[k] if 0 <= k <= K else mp.mpc(0)
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            # indices 1-based: h_{l_i - i + j} + h_{l_i - i - j + 2}
            M[i, j] = H(lamp[i] - (i + 1) + (j + 1)) + H(lamp[i] - (i + 1) - (j + 1) + 2)
    val = mdet(M) / 2
    mp.mp.dps = old
    return +val


def spectrum_gpq(m, p, q):
    return [(p * j) % q for j in range(1, m + 1)] + [(-p * j) % q for j in range(1, m + 1)]


def mdet(M):
    """determinante por eliminacion gaussiana con pivote maximo (mpmath), tolera matrices singulares."""
    n = M.rows; A = [[M[i, j] for j in range(n)] for i in range(n)]; d = mp.mpc(1)
    for k in range(n):
        p = max(range(k, n), key=lambda i: abs(A[i][k]))
        if A[p][k] == 0:
            return mp.mpc(0)
        if p != k:
            A[k], A[p] = A[p], A[k]; d = -d
        d *= A[k][k]
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            if f:
                for j in range(k, n):
                    A[i][j] -= f * A[k][j]
    return d


# ---------------- (WD) Weyl determinante en punto regular ----------------
def chi_weyl_sp(lam, xs):
    s = len(lam); r = rho(s); l = [lam[i] + r[i] for i in range(s)]
    A = mp.matrix(s, s); C = mp.matrix(s, s)
    for i in range(s):
        for j in range(s):
            A[i, j] = xs[j] ** l[i] - xs[j] ** (-l[i]); C[i, j] = xs[j] ** r[i] - xs[j] ** (-r[i])
    return mp.det(A) / mp.det(C)


def chi_weyl_so_even(mu, xs):
    s = len(mu); r = [s - 1 - i for i in range(s)]; l = [mu[i] + r[i] for i in range(s)]
    A = mp.matrix(s, s); B = mp.matrix(s, s); C = mp.matrix(s, s)
    for i in range(s):
        for j in range(s):
            A[i, j] = xs[j] ** l[i] + xs[j] ** (-l[i]); B[i, j] = xs[j] ** l[i] - xs[j] ** (-l[i])
            C[i, j] = xs[j] ** r[i] + xs[j] ** (-r[i])
    return (mp.det(A) + mp.det(B)) / mp.det(C)


# ---------------- estadisticos del paper (desde sus definiciones) ----------------
def Nq(x, q):
    return sum(1 for a in root_vals(x) if a % q == 0)


def Zq(x, q):
    r = 1
    for a in root_vals(x):
        if a % q == 0:
            r *= a
    return r


def Epq(lam, p, q):
    m = len(lam); r = rho(m); l = [lam[i] + r[i] for i in range(m)]
    return sum((p * a) // q for a in root_vals(l)) - sum((p * b) // q for b in root_vals(r))


def pure(lam, p, q):
    m = len(lam); r = rho(m); l = [lam[i] + r[i] for i in range(m)]
    return (-1) ** (Epq(lam, p, q) % 2) * Fraction(Zq(l, q), Zq(r, q))


# ---------------- dimensiones y Delta_lambda ----------------
def dim_GL(nu):
    n = len(nu); r = Fraction(1)
    for i in range(n):
        for j in range(i + 1, n):
            r *= Fraction(nu[i] - nu[j] + j - i, j - i)
    return r


def _dimBC(a, r0):
    num = Fraction(1); den = Fraction(1); n = len(a)
    for i in range(n):
        num *= a[i]; den *= r0[i]
        for j in range(i + 1, n):
            num *= (a[i] ** 2 - a[j] ** 2); den *= (r0[i] ** 2 - r0[j] ** 2)
    return num / den


def dim_Sp(nu):
    n = len(nu); r0 = [Fraction(n - i) for i in range(n)]
    return _dimBC([nu[i] + r0[i] for i in range(n)], r0)


def dim_SOodd(nu):
    n = len(nu); r0 = [Fraction(2 * (n - i) - 1, 2) for i in range(n)]
    return _dimBC([nu[i] + r0[i] for i in range(n)], r0)


def classes_of(l, q):
    """agrupa entradas en clases plegadas c=min(r,q-r). devuelve dict c->lista de entradas."""
    d = {}
    for x in l:
        r = x % q; c = min(r, q - r)
        d.setdefault(c, []).append(x)
    return d


def Delta(lam, q):
    """producto de dimensiones del Teorema B (definiciones previas al Teorema B), desde cero."""
    m = len(lam); r = rho(m); l = [lam[i] + r[i] for i in range(m)]
    D = Fraction(1); labels = {}
    for c, xs in classes_of(l, q).items():
        n = len(xs)
        if c == 0:
            z = sorted([Fraction(x, q) for x in xs], reverse=True)
            nu = [z[i] - (n - i) for i in range(n)]
            assert all(t.denominator == 1 for t in nu)
            D *= dim_Sp(nu); labels[c] = ('Sp', [int(t) for t in nu])
        elif 2 * c == q:
            z = sorted([Fraction(x, q) for x in xs], reverse=True)
            nu = [z[i] - (n - i) + Fraction(1, 2) for i in range(n)]
            assert all(t.denominator == 1 for t in nu)
            D *= dim_SOodd(nu); labels[c] = ('SO', [int(t) for t in nu])
        else:
            ys = []
            for x in xs:
                e = 1 if x % q == c else -1
                ys.append((e * x - c) // q)
                assert (e * x - c) % q == 0
            ys.sort(reverse=True)
            nu = [ys[i] - ys[-1] - (n - 1 - i) for i in range(n)]
            D *= dim_GL(nu); labels[c] = ('GL', nu)
    for _, (_, nu) in labels.items():
        assert all(nu[i] >= nu[i + 1] for i in range(len(nu) - 1)) and (not nu or nu[-1] >= 0), (lam, q, labels)
    return D, labels


def families(m, q):
    f = []
    if m % q == 0: f.append('q|m')
    if (2 * m) % q == 0 and m % q != 0: f.append('q|2m,q∤m')
    if (2 * m + 1) % q == 0: f.append('q|2m+1')
    if (2 * m + 2) % q == 0: f.append('q|2m+2')
    if q == 6 and m % 6 == 1: f.append('q=6,m≡1(6)')
    if q == 6 and m % 6 == 4: f.append('q=6,m≡4(6)')
    return f
