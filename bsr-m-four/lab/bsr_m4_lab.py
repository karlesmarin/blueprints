# encaje: laboratorios del blueprint bsr-m-four (Figuras 1, 2, 3 y 5 del paper «Every m×4 biquadratic sum of squares is
# a sum of 3m−1 squares (5 ≤ m ≤ 16)»). Los cálculos son los de research/cohete-sat/z2/bsr_m4/paper/laboratorio.py
# (copiados aquí porque Pyodide no ve ese fichero); la búsqueda local usa un Nelder–Mead propio en numpy en vez de
# scipy (no carga scipy en el navegador). lab/comprueba_lab.py los coteja con figuras.salida.txt.
# Miré el catálogo: labweb (prueba los labs en el navegador, no calcula figuras), la puerta de novedad numérica
# (compara cotas publicadas, no dibuja) y la comprobación simbólica con sympy (identidades del paper, no figuras):
# ninguna calcula estas figuras; labweb se usa después para probarlas.
"""Labs of «Every m×4 biquadratic sum of squares is a sum of 3m−1 squares (5 ≤ m ≤ 16)».

    run_bounds    Figure 1: the bounds on BSR(m,4) against m (this paper, 3m, lower bounds, known values, r_P)
    run_gram      Figure 2: the Gram spectrahedron of a 2×3 biquadratic sum of squares, its boundary and its
                  numerically rank-four points (a numerical illustration in floating point, as in the paper)
    run_inertia   Figure 3: the real bound q_* of the boundary inertia inequality over (m, N/m), exact along a line
    run_triples   Figure 5: the candidate support triples (a, b, r) and the step of the proof that excludes each

Numbers that are not computed here are the lower bounds of the paper's table for m = 5, 6, 7 (z_2(m,4) = 13, 16, 19,
from the literature the paper cites) and the known values BSR(m,4) = 5, 8, 11 for m = 2, 3, 4."""
import json
import random
from fractions import Fraction
from itertools import product
from math import comb, floor, sqrt

import labkit as K

AZUL, NARANJA, VERDE, CIELO, AMARILLO, BERMELLON, PURPURA, GRIS = (
    '#0072B2', '#E69F00', '#009E73', '#56B4E9', '#C9B800', '#D55E00', '#CC79A7', '#999999')


# ----------------------------------------------------------------------------------------------- counts of the paper
def dim_R2(m, n=4):
    """M = dim R_2 = C(m+1,2) C(n+1,2); for n = 4, M = 5m(m+1)."""
    return comb(m + 1, 2) * comb(n + 1, 2)


def q_star(m, N):
    """The real bound q_* = 1 + (5m(m+1) − C(N+2,2))/N of the boundary inertia inequality N(q−1) ≤ M − C(N+2,2),
    exact (a Fraction) for integer m, N."""
    return 1 + Fraction(dim_R2(m) - comb(N + 2, 2), N)


def q_star_real(m, c):
    """The same with N = c·m real (the surface of Figure 3)."""
    N = c * m
    return 1 + (5 * m * (m + 1) - (N + 2) * (N + 1) / 2) / N


def level_N(m, k):
    """N with q_*(m, N) = k: the positive root of N² + (2k+1)N + 2 − 2M = 0."""
    M = 5 * m * (m + 1)
    return (-(2 * k + 1) + sqrt((2 * k + 1) ** 2 - 8 + 8 * M)) / 2


def r_pataki(m, n=4):
    """The Barvinok–Pataki rank max{r : C(r+1,2) ≤ dim R_2}."""
    M = dim_R2(m, n)
    r = 1
    while comb(r + 2, 2) <= M:
        r += 1
    return r


LITERATURE_LOW = {5: 13, 6: 16, 7: 19}   # z_2(m,4): Löfberg–Qi (m = 5, 6), Xu–Yan (m = 7), as cited in Section 1
KNOWN = {2: 5, 3: 8, 4: 11}              # BSR(m,4) for m = 2, 3, 4 (BPSV, [Mar3], [Mar44]), the base of the induction


def lower_bound(m):
    """The lower bound of the table of Section 1 (5 ≤ m ≤ 16): z_2 for m ≤ 7; ⌊8m/3⌋ (quadratic persistence) for
    8 ≤ m ≤ 14; the exact z_2(m,4) = ⌊(5m+6)/2⌋ of Chen–Chen for m = 15, 16. None outside 5..16."""
    if m in LITERATURE_LOW:
        return LITERATURE_LOW[m]
    if 8 <= m <= 14:
        return 8 * m // 3
    if m in (15, 16):
        return (5 * m + 6) // 2
    return None


# ------------------------------------------------------------------------------------------- the support triples
CLASSES = [  # (key, label, colour), in the order of the proof of the theorem for 5 ≤ m ≤ 16
    ('small', 'small supports: a ≤ 2 or b ≤ 2', GRIS),
    ('weak', 'r ≤ a: weak low-index inequality', PURPURA),
    ('compression', 'a ≤ m−2: compression', AZUL),
    ('strong', 'b = 4, r = a+1: low-index lemma', NARANJA),
    ('psi4', '(m−1, 4, m+1): rank of Ψ', VERDE),
    ('psi3', '(m, 3, m+1): rank of Ψ, factors exchanged', CIELO),
    ('syzygy', '(m−1, 3, m+1): syzygy from (R)', AMARILLO),
    ('last', '(m−1, 3, m): rank of Ψ or (R)', BERMELLON),
]
LAST4 = ('psi4', 'psi3', 'syzygy', 'last')


def triple_class(m, a, b, r):
    """The step of the proof that excludes (a, b, r): small supports; r ≥ a + 1 (weak inequality); compression if
    a ≤ m − 2; r ≥ a + 2 if b = 4 (low-index lemma); then the four remaining triples, each with its own argument.
    Raises KeyError if a triple falls in no class (the partition would be incomplete)."""
    if a <= 2 or b <= 2:
        return 'small'
    if r <= a:
        return 'weak'
    if a <= m - 2:
        return 'compression'
    if b == 4 and r == a + 1:
        return 'strong'
    return {(m - 1, 4, m + 1): 'psi4', (m, 3, m + 1): 'psi3', (m - 1, 3, m + 1): 'syzygy',
            (m - 1, 3, m): 'last'}[(a, b, r)]


def triples(m):
    """{class: [(a, b, r), ...]} over 1 ≤ a ≤ m, 1 ≤ b ≤ 4, 1 ≤ r ≤ m + 1 (rank H ≤ dim V − N = m + 1)."""
    out = {k: [] for k, _, _ in CLASSES}
    for a, b, r in product(range(1, m + 1), range(1, 5), range(1, m + 2)):
        out[triple_class(m, a, b, r)].append((a, b, r))
    return out


# ------------------------------------------------------------------------------------------ the Gram spectrahedron
def _np():
    import numpy as np
    return np


def form_2x3(seed=5):
    """The integer 6×6 matrix V of the paper's script (figuras.forma_2x3): entries in {−2, …, 2}, redrawn until
    invertible. F = Σ_k (Σ_c V[k, c] x_{c//3} y_{c%3})², a sum of six squares of bilinear forms in 2 + 3 variables."""
    np = _np()
    rng = np.random.default_rng(seed)
    V = rng.integers(-2, 3, size=(6, 6)).astype(float)
    while abs(np.linalg.det(V)) < 1:
        V = rng.integers(-2, 3, size=(6, 6)).astype(float)
    return V


def _monomial(a, b, n):
    return (tuple(sorted((a // n, b // n))), tuple(sorted((a % n, b % n))))


def gram_kernel(m, n):
    """Basis of the symmetric matrices X with v^T X v = 0 (v = x ⊗ y), each of norm 1, and the number of monomials."""
    np = _np()
    C = m * n
    idx = [(i, j) for i in range(C) for j in range(i, C)]
    mon = sorted({_monomial(i, j, n) for i, j in idx})
    pos = {mo: t for t, mo in enumerate(mon)}
    A = np.zeros((len(mon), len(idx)))
    for t, (i, j) in enumerate(idx):
        A[pos[_monomial(i, j, n)], t] = 1.0 if i == j else 2.0
    _, s, Vt = np.linalg.svd(A)
    rk = int((s > 1e-10).sum())
    L = []
    for v in Vt[rk:]:
        X = np.zeros((C, C))
        for t, (i, j) in enumerate(idx):
            X[i, j] = X[j, i] = v[t]
        L.append(X / np.linalg.norm(X))
    return np.array(L), len(mon)


class Spectrahedron:
    """The Gram matrices G0 + Σ t_i L_i ⪰ 0 of F (G0 = VᵀV). boundary(dirs): for unit directions d, the boundary point
    s(d)·d where G0 + s D first becomes singular, and the eigenvalues there (vectorised)."""

    def __init__(self, m, n, V):
        np = _np()
        self.V = np.asarray(V, dtype=float)
        self.G0 = self.V.T @ self.V
        self.L, self.monomials = gram_kernel(m, n)
        self.dim = len(self.L)
        w0, U0 = np.linalg.eigh(self.G0)
        if w0.min() <= 1e-10:
            raise ValueError('G0 is not positive definite')
        self.R = U0 @ np.diag(w0 ** -0.5) @ U0.T

    def boundary(self, dirs):
        np = _np()
        dirs = np.atleast_2d(np.asarray(dirs, dtype=float))
        dirs = dirs / np.linalg.norm(dirs, axis=1, keepdims=True)
        D = np.tensordot(dirs, self.L, axes=(1, 0))                    # (k, 6, 6)
        lam = np.linalg.eigvalsh(-self.R @ D @ self.R)[:, -1]
        s = 1.0 / lam                                                 # lam > 0: the Gram spectrahedron is compact
        ev = np.linalg.eigvalsh(self.G0 + s[:, None, None] * D)
        return s[:, None] * dirs, ev


def nelder_mead(f, x0, step=0.1, iters=1500, xtol=1e-12, ftol=1e-15):
    """Plain Nelder–Mead (the standard coefficients 1, 2, 1/2, 1/2), as a replacement for scipy's in the browser."""
    np = _np()
    n = len(x0)
    S = [np.array(x0, dtype=float)]
    for i in range(n):
        x = np.array(x0, dtype=float)
        x[i] = x[i] + (step if x[i] == 0 else step * abs(x[i]) + step)
        S.append(x)
    F = [f(x) for x in S]
    for _ in range(iters):
        o = sorted(range(n + 1), key=lambda i: F[i])
        S, F = [S[i] for i in o], [F[i] for i in o]
        if max(np.abs(S[i] - S[0]).max() for i in range(1, n + 1)) <= xtol and F[-1] - F[0] <= ftol:
            break
        c = sum(S[:-1]) / n
        xr = c + (c - S[-1]); fr = f(xr)
        if fr < F[0]:
            xe = c + 2 * (c - S[-1]); fe = f(xe)
            S[-1], F[-1] = (xe, fe) if fe < fr else (xr, fr)
        elif fr < F[-2]:
            S[-1], F[-1] = xr, fr
        else:
            xc = c + 0.5 * (S[-1] - c) if fr >= F[-1] else c + 0.5 * (xr - c)
            fc = f(xc)
            if fc < min(fr, F[-1]):
                S[-1], F[-1] = xc, fc
            else:
                S = [S[0]] + [S[0] + 0.5 * (x - S[0]) for x in S[1:]]
                F = [F[0]] + [f(x) for x in S[1:]]
    i = int(np.argmin(F))
    return S[i], F[i]


def low_rank_points(E, starts=25, rng_seed=0):
    """The paper's search (laboratorio.rango_minimo_frontera): minimise λ_2 (on the boundary λ_1 = 0) over the
    directions, from the `starts` best of 2000 random rays (generator seed 0). Returns the distinct local minima
    [(t, eigenvalues)], sorted by λ_2."""
    np = _np()
    dirs = np.random.default_rng(rng_seed).standard_normal((2000, E.dim))
    _, ev = E.boundary(dirs)

    def lam2(d):
        if not np.all(np.isfinite(d)) or np.linalg.norm(d) == 0:
            return np.inf
        return E.boundary([d])[1][0][1]

    out = []
    for i in np.argsort(ev[:, 1])[:starts]:
        d, _ = nelder_mead(lam2, dirs[i] / np.linalg.norm(dirs[i]))
        p, e = E.boundary([d])
        out.append((p[0], e[0]))
    out.sort(key=lambda x: x[1][1])
    uniq = []
    for p, e in out:
        if all(np.linalg.norm(p - q) > 1e-3 for q, _ in uniq):
            uniq.append((p, e))
    return uniq


def sphere_dirs(nt):
    """nt × 2nt directions on a (θ, φ) grid (the paper: nt = 70, 9800 rays)."""
    np = _np()
    th, ph = np.meshgrid(np.linspace(0, np.pi, nt), np.linspace(0, 2 * np.pi, 2 * nt), indexing='ij')
    return np.stack([np.sin(th) * np.cos(ph), np.sin(th) * np.sin(ph), np.cos(th)], axis=-1).reshape(-1, 3), th.shape


def _pad3(items, f=0.3):
    """Two invisible points that widen the 3D box, so that nothing is cut at any angle (as in robust-offset)."""
    lo, hi = [float('inf')] * 3, [float('-inf')] * 3
    for it in items:
        pts = [v for row in it['grid'] for v in row] if it['type'] == 'surface' else it['points']
        for v in pts:
            for i in range(3):
                lo[i], hi[i] = min(lo[i], v[i]), max(hi[i], v[i])
    r = max(hi[i] - lo[i] for i in range(3)) or 1.0
    return list(items) + [K.points3([[lo[i] - f * r for i in range(3)], [hi[i] + f * r for i in range(3)]], '',
                                    color='#ffffff', size=1, opacity=0.0)]


def _frac(q):
    return '%d/%d' % (q.numerator, q.denominator) if q.denominator != 1 else str(q.numerator)


# ----------------------------------------------------------------------------------------------------------- labs
def run_bounds(params):
    p = json.loads(params)
    try:
        lo, hi = int(p.get('mlo', 2)), int(p.get('mhi', 22))
    except ValueError:
        return K.error('The range of m must be two integers.')
    if not (2 <= lo < hi <= 60):
        return K.error('Choose 2 ≤ first m < last m ≤ 60.')
    ms = list(range(lo, hi + 1))
    thm = [m for m in ms if 5 <= m <= 16]
    low = [m for m in ms if lower_bound(m) is not None]
    known = [m for m in ms if m in KNOWN]
    first5 = next((m for m in range(5, 200) if floor(q_star(m, 3 * m - 1)) >= 5), None)
    series = [{'name': 'Barvinok–Pataki r_P', 'x': ms, 'y': [r_pataki(m) for m in ms], 'mode': 'line', 'color': VERDE},
              {'name': 'previous bound 3m', 'x': ms, 'y': [3 * m for m in ms], 'mode': 'line', 'color': GRIS}]
    if thm:
        series.append({'name': 'this paper: 3m − 1 (5 ≤ m ≤ 16)', 'x': thm, 'y': [3 * m - 1 for m in thm],
                       'mode': 'line', 'color': AZUL})
        series.append({'name': '', 'x': thm, 'y': [3 * m - 1 for m in thm], 'mode': 'points', 'color': AZUL, 'size': 3})
    if low:
        series.append({'name': 'lower bounds (table of Section 1)', 'x': low, 'y': [lower_bound(m) for m in low],
                       'mode': 'points', 'color': BERMELLON, 'size': 3.5})
    if known:
        series.append({'name': 'known BSR(m,4) = 5, 8, 11', 'x': known, 'y': [KNOWN[m] for m in known],
                       'mode': 'points', 'color': '#000000', 'size': 4.5})
    if lo <= 16 < hi:
        series.append({'name': 'm = 16.5: beyond it the inertia bound allows q = 5', 'x': [16.5, 16.5],
                       'y': [0, 3 * hi], 'mode': 'line', 'color': '#BBBBBB'})
    fig = K.svg_plot(series, title='Bounds on BSR(m,4), m = %d … %d' % (lo, hi), xlabel='m (rows)',
                     ylabel='number of squares', figure='paperfig-1')
    rows = []
    for m in ms:
        q = q_star(m, 3 * m - 1)
        rows.append([m, (3 * m - 1) if 5 <= m <= 16 else '—', 3 * m, lower_bound(m) if lower_bound(m) else
                     (KNOWN[m] if m in KNOWN else '—'), r_pataki(m), r_pataki(m) - (3 * m - 1),
                     (3 * m - 1 - lower_bound(m)) if lower_bound(m) else '—',
                     '%s ≈ %.3f' % (_frac(q), float(q)) if m >= 5 else '—', floor(q) if m >= 5 else '—'])
    gaps = [3 * m - 1 - lower_bound(m) for m in thm]
    over = [r_pataki(m) - (3 * m - 1) for m in thm]
    txt = ('For m = %d … %d. Theorem 1 gives BSR(m,4) ≤ 3m − 1 only for 5 ≤ m ≤ 16 (%s in this range). '
           % (lo, hi, ('%d values' % len(thm)) if thm else 'none'))
    if thm:
        txt += ('There the gap to the lower bound of the table is %s, and the Barvinok–Pataki rank r_P exceeds 3m − 1 '
                'by %s, so it does not give the theorem. ' % (', '.join(map(str, gaps)), ', '.join(map(str, over))))
    txt += ('The method stops at m = %d: along N = 3m − 1 the real bound q_* = 1 + (5m(m+1) − C(N+2,2))/N reaches 5 '
            'there (q_* = %s), and the low-negative-index lemma needs q ≤ 4. The values 5, 8, 11 for m = 2, 3, 4 lie '
            'on the line 3m − 1; the induction uses them. Lower bounds for m = 5, 6, 7 are z₂(m,4) from the '
            'literature the paper cites; for 8 ≤ m ≤ 14 the lab computes ⌊8m/3⌋ and for m = 15, 16 ⌊(5m+6)/2⌋, the '
            'rules stated in Section 1.' % (first5, _frac(q_star(first5, 3 * first5 - 1))))
    return K.result(txt, [fig], K.table(['m', 'this paper', 'previous 3m', 'lower / known', 'r_P', 'r_P − (3m−1)',
                                         'gap', 'q_* at N = 3m−1', '⌊q_*⌋'], rows))


def random_bounds():
    lo = random.randint(2, 30)
    return json.dumps({'mlo': str(lo), 'mhi': str(random.randint(lo + 1, min(60, lo + 30)))})


def run_gram(params):
    p = json.loads(params)
    try:
        seed, nt, starts = int(p.get('seed', 5)), int(p.get('rays', 70)), int(p.get('starts', 25))
    except ValueError:
        return K.error('The seed, the rays and the searches must be integers.')
    if not (0 <= seed <= 9999 and 8 <= nt <= 70 and 1 <= starts <= 40):
        return K.error('Choose 0 ≤ seed ≤ 9999, 8 ≤ rays per half-circle ≤ 70 (70 is the paper: 9800 rays) and '
                       '1 ≤ local searches ≤ 40.')
    np = _np()
    V = form_2x3(seed)
    E = Spectrahedron(2, 3, V)
    dirs, shape = sphere_dirs(nt)
    P, ev = E.boundary(dirs)
    ratio = ev[:, 1] / ev[:, -1]
    lam1 = float(np.abs(ev[:, 0]).max())
    low = low_rank_points(E, starts)
    rank4 = [(t, e) for t, e in low if e[1] < 1e-8 * e[-1]]
    col = np.log10(np.clip(ratio, 1e-6, 1))
    c0, c1 = float(col.min()), float(col.max())
    Pg = P.reshape(shape + (3,))
    Cg = col.reshape(shape)
    grid = [[[round(float(v), 4) for v in Pg[i, j]] for j in range(shape[1])] for i in range(shape[0])]
    cols = [[K.scale(float(Cg[i, j]), c0, c1, 'sequential') for j in range(shape[1])] for i in range(shape[0])]
    items = [{'type': 'surface', 'grid': grid, 'colors': cols, 'name': 'boundary (colour: log10 λ2/λ6)',
              'color': '#c9d6e3', 'opacity': 0.85}]
    if rank4:
        items.append(K.points3([[round(float(v), 4) for v in t] for t, _ in rank4],
                               'numerically rank-four points (%d)' % len(rank4), color=BERMELLON, size=9, star=True))
    td = K.three_d(_pad3(items), 'Gram spectrahedron of F (seed %d): %d rays, %d rank-four points found'
                   % (seed, len(dirs), len(rank4)), axes=('t₁', 't₂', 't₃'),
                   colorbar=K.colorbar('log10(λ2/λ6) on the boundary (low: near rank 4)', c0, c1, 'sequential'))
    td['figure'] = 'paperfig-2'
    Vi = V.astype(int)
    rows = [[k + 1, ' '.join('%.4f' % v for v in t), ' '.join('%.1e' % v for v in e)] for k, (t, e) in enumerate(low)]
    txt = ('F = Σ_k ((row k of V)·(x ⊗ y))² with the integer matrix V of seed %d (rows %s). Its Gram matrices G with '
           'F = vᵀGv, v = x ⊗ y, form the affine family G0 + t₁L₁ + t₂L₂ + t₃L₃ (21 entries, %d monomials: kernel of '
           'dimension %d), cut by G ⪰ 0. On all %d rays drawn the boundary point has one numerically zero eigenvalue '
           '(max |λ1| = %.1e) and min λ2/λ6 = %.1e%s. The local search from the %d best of 2000 random rays '
           'finds %d distinct local minima of λ2, of which %d have λ2 < 1e-8·λ6: numerically rank-four points, i.e. '
           'representations of F by four squares (four is BSR(2,3)). This is floating point, not a proof: a search '
           'with fewer starts can miss some of them. Theorem 1 says, in this language, that the Gram spectrahedron '
           'of every m×4 sum of squares, 5 ≤ m ≤ 16, contains a point of rank at most 3m − 1.'
           % (seed, '; '.join(' '.join('%d' % x for x in r) for r in Vi), E.monomials, E.dim, len(dirs), lam1,
              float(ratio.min()), ', so every drawn boundary point has numerical rank 5' if ratio.min() > 1e-8 else
              ': some rays land numerically on rank 4', starts, len(low), len(rank4)))
    return K.result(txt, [td], K.table(['local minimum', 't = (t₁, t₂, t₃)', 'eigenvalues λ1 … λ6'], rows))


def random_gram():
    return json.dumps({'seed': str(random.randint(0, 9999)), 'rays': str(random.choice([40, 50, 60, 70])),
                       'starts': str(random.randint(5, 25))})


def run_inertia(params):
    p = json.loads(params)
    try:
        mhi = int(p.get('mhi', 24))
        c = float(Fraction(str(p.get('c', '3')).strip()))
        d = int(p.get('d', -1))
    except (ValueError, ZeroDivisionError):
        return K.error('m, the offset d must be integers and N/m a number (3 or 2.8 or 17/6).')
    if not (8 <= mhi <= 60 and 2.0 <= c <= 4.0 and -10 <= d <= 10):
        return K.error('Choose 8 ≤ last m ≤ 60, 2 ≤ N/m ≤ 4 and −10 ≤ d ≤ 10.')
    ms = list(range(5, mhi + 1))
    Ns = [int(round(c * m + d)) for m in ms]
    if min(Ns) < 1:
        return K.error('N = round(c·m + d) must be positive.')
    qs = [q_star(m, N) for m, N in zip(ms, Ns)]
    ok = [m for m, q in zip(ms, qs) if floor(q) <= 4]
    first5 = next((m for m, q in zip(ms, qs) if floor(q) >= 5), None)
    # 2D: the level sets q_* = k in the (m, N/m) plane (the right panel of Figure 3) and your line
    xs = [5 + (mhi - 5) * i / 120 for i in range(121)]
    series = []
    lev_col = {2: '#9ecae1', 3: '#6baed6', 4: '#2171b5', 5: '#000000', 6: '#8c6bb1', 7: '#88419d'}
    for k in (2, 3, 4, 5, 6, 7):
        pts = [(x, level_N(x, k) / x) for x in xs]
        pts = [(x, y) for x, y in pts if 2.5 <= y <= 3.5]
        if pts:
            series.append({'name': 'q_* = %d' % k, 'x': [a for a, _ in pts], 'y': [b for _, b in pts], 'mode': 'line',
                           'color': lev_col[k]})
    series.append({'name': 'your line N = round(%g·m %+d)' % (c, d), 'x': ms, 'y': [N / m for m, N in zip(ms, Ns)],
                   'mode': 'line', 'color': BERMELLON})
    series.append({'name': '⌊q_*⌋ ≤ 4 on your line', 'x': ok, 'y': [N / m for m, N in zip(ms, Ns) if m in ok],
                   'mode': 'points', 'color': BERMELLON, 'size': 3.5})
    fig = K.svg_plot(series, title='Level sets of the real bound q_* over (m, N/m)', xlabel='m', ylabel='N/m',
                     figure='paperfig-3')
    # 2D bis: q_* along the line
    fig2 = K.svg_plot([{'name': 'q_* along your line', 'x': ms, 'y': [float(q) for q in qs], 'mode': 'line',
                        'color': BERMELLON},
                       {'name': '⌊q_*⌋', 'x': ms, 'y': [floor(q) for q in qs], 'mode': 'points', 'color': '#000000',
                        'size': 2.5},
                       {'name': 'q = 4 (what the low-index lemma covers)', 'x': [5, mhi], 'y': [4, 4], 'mode': 'line',
                        'color': AZUL}],
                      title='q_* along N = round(%g·m %+d)' % (c, d), xlabel='m', ylabel='real bound q_*')
    # 3D: the surface q_*(m, N/m), coloured by ⌊q_*⌋ (the level sets), with the line and the level q_* = 5
    cs = [2.6 + 0.8 * j / 24 for j in range(25)]
    mg = [5 + (mhi - 5) * i / 30 for i in range(31)]
    zs = lambda m, cc: max(0.0, min(9.0, q_star_real(m, cc)))
    floors = {0: '#440154', 1: '#46327e', 2: '#365c8d', 3: '#277f8e', 4: '#1fa187', 5: '#4ac16d', 6: '#a0da39',
              7: '#fde725', 8: '#fde725', 9: '#fde725'}
    surf = K.surface3(zs, mg, cs, name='q_*(m, N/m), coloured by ⌊q_*⌋', opacity=0.8,
                      colorfn=lambda x, y, z: floors[int(floor(z))])
    line = K.curve3([[m, N / m, max(0.0, min(9.0, float(q)))] for m, N, q in zip(ms, Ns, qs)], 'your line',
                    color=BERMELLON, width=3)
    lev = K.curve3([[x, level_N(x, 5) / x, 5.0] for x in mg if 2.6 <= level_N(x, 5) / x <= 3.4], 'q_* = 5',
                   color='#ffffff', width=2)
    dots = K.points3([[m, N / m, float(q)] for m, N, q in zip(ms, Ns, qs) if m in ok], '⌊q_*⌋ ≤ 4', color='#ffffff',
                     size=6)
    td = K.three_d(_pad3([surf, line, lev, dots]), 'The real bound q_* over (m, N/m)', axes=('m', 'N/m', 'q_*'),
                   colorbar=K.colorbar('⌊q_*⌋', stops=[[str(k), floors[k]] for k in range(1, 8)]))
    rows = [[m, N, dim_R2(m), dim_R2(m) - comb(N + 2, 2), '%s ≈ %.4f' % (_frac(q), float(q)), floor(q)]
            for m, N, q in zip(ms, Ns, qs)]
    span = ('%d … %d' % (ok[0], ok[-1]) if ok and ok == list(range(ok[0], ok[-1] + 1)) else
            ', '.join(map(str, ok)) if ok else 'no m')
    txt = ('Along N = round(%g·m %+d): ⌊q_*⌋ ≤ 4 for m = %s; ' % (c, d, span) +
           ('the first m with ⌊q_*⌋ ≥ 5 is %d (q_* = %s). ' % (first5, _frac(qs[ms.index(first5)])) if first5 else
            'no m up to %d reaches 5. ' % mhi) +
           'Here q_* = 1 + (M − C(N+2,2))/N with M = 5m(m+1), the real bound of the boundary inertia inequality '
           'N(q−1) ≤ M − C(N+2,2), so the negative index satisfies q ≤ ⌊q_*⌋. ')
    if abs(c - 3) < 1e-12 and d == -1:
        txt += ('This is the paper’s line N = 3m − 1: the room M − C(N+2,2) is exactly m(m+7)/2, q_* = 22/7 at m = 5, '
                '231/47 at m = 16 and 127/25 at m = 17, so ⌊q_*⌋ ≤ 4 exactly for 5 ≤ m ≤ 16, the range of Theorem 1. ')
    txt += ('The level curves are N with q_*(m, N) = k, the positive root of N² + (2k+1)N + 2 − 2M = 0. The 3D '
            'surface is coloured by ⌊q_*⌋; the white curve is q_* = 5.')
    return K.result(txt, [fig, fig2, td], K.table(['m', 'N', 'M = 5m(m+1)', 'room M − C(N+2,2)', 'q_*', '⌊q_*⌋'],
                                                  rows))


def random_inertia():
    return json.dumps({'mhi': str(random.randint(10, 40)), 'c': random.choice(['3', '2.9', '3.1', '2.8', '17/6']),
                       'd': str(random.randint(-3, 2))})


def run_triples(params):
    p = json.loads(params)
    try:
        m = int(p.get('m', 10))
    except ValueError:
        return K.error('m must be an integer.')
    if not 5 <= m <= 16:
        return K.error('Choose 5 ≤ m ≤ 16, the range of the theorem: at m = 17 the inertia bound allows q = 5 and the '
                       'low-negative-index lemma (q ≤ 4) no longer applies, so this partition is not a proof there.')
    T = triples(m)
    total = sum(len(v) for v in T.values())
    items = []
    for k, label, colr in CLASSES:
        pts = [[a, r, b] for a, b, r in T[k]]
        if pts:
            big = k in LAST4 or k == 'strong'
            items.append(K.points3(pts, '%s (%d)' % (label, len(pts)), color=colr, size=9 if big else 4,
                                   star=k in LAST4, opacity=0.95 if big else (0.25 if k == 'small' else 0.6)))
    td = K.three_d(items, 'm = %d: the %d candidate triples (a, b, r), by the step that excludes them' % (m, total),
                   axes=('row support a', 'rank r', 'column support b'))
    td['figure'] = 'paperfig-5'
    series = []
    for k, label, colr in CLASSES:
        pts = [(a + (0.18 if b == 4 else -0.18), r) for a, b, r in T[k] if b >= 3]
        if pts:
            series.append({'name': label, 'x': [x for x, _ in pts], 'y': [y for _, y in pts], 'mode': 'points',
                           'color': colr, 'size': 4.5 if k in LAST4 or k == 'strong' else 2.5})
    fig = K.svg_plot(series, title='m = %d, b ∈ {3, 4} (b = 3 left of each a, b = 4 right)' % m,
                     xlabel='row support a', ylabel='rank r')
    rows = [[label, len(T[k]), ', '.join('(%d,%d,%d)' % t for t in T[k]) if k in LAST4 or k == 'strong' else '']
            for k, label, _ in CLASSES]
    txt = ('For m = %d there are 4m(m+1) = %d candidate triples (a, b, r): 1 ≤ a ≤ m, 1 ≤ b ≤ 4 and r ≤ m + 1 '
           '(the rank budget dim V − N). Each falls in exactly one class: %s. Small supports, the weak inequality '
           'r ≥ a + 1 and compression (which needs BSR(m−a,4) ≤ 3(m−a) − 1, so a ≤ m − 2) leave six triples; the '
           'low-index lemma (r ≥ a + 2 when b = 4) removes (m,4,m+1) and (m−1,4,m), and the last four each need '
           'their own argument. The triples are candidates, not all realised by multipliers.'
           % (m, total, ', '.join('%s %d' % (k, len(T[k])) for k, _, _ in CLASSES)))
    return K.result(txt, [td, fig], K.table(['class (step of the proof)', 'triples', 'which'], rows))


def random_triples():
    return json.dumps({'m': str(random.randint(5, 16))})


if __name__ == '__main__':
    import time
    for f, a in ((run_bounds, {}), (run_inertia, {}), (run_triples, {'m': '10'}), (run_gram, {})):
        t = time.time()
        r = json.loads(f(json.dumps(a)))
        print(f.__name__, '%.1fs' % (time.time() - t), r.get('error') or r['text'][:600])
