# encaje: laboratorio del blueprint prescribed-moments-II (corre en el navegador con Pyodide; Python puro, sin dependencias).
"""Labs of «Subsets of F_p with two prescribed moments, Part II»: the seven computed figures of the paper, live.

Everything is computed here, nothing is typed from a table:
  run_grid      Figure 1   the classification of Theorem 8 as a grid, and the counts C_k(n,p) of one cell, enumerated
  run_collapse  Figure 3   S_m (the n whose length-four strata are all singular) from the definition, against gcd(m,6)
  run_genus     Figure 4   the two witnesses of the proof of Theorem 8: arithmetic genus, singular points, genus
  run_values    Figure 5   every value of 6 C_k(3,p)/(p-1), prime by prime
  run_degree    Figure 6   deg Q_k from s_k, against floor(k/6) - [k = 1 mod 6] and dim M_2k(SL_2(Z))
  run_primes    Figure 7   the split primes of a cubic (Chebotarev) and the traces a_p of y^2 = x^3 + x^2 - x
  run_circle    Figure 8   step one of Appendix A: the sign changes of s_k(theta) and the values u(theta) they land on

The column n = 3 is counted in O(p): scaling by t in F_p^* acts freely on the ordered triples, so
6 C_k(3,p)/(p-1) = #{y : 1, y, -1-y distinct, 1 + y^k + (-1-y)^k = 0} + [k odd]
(the second term: the triples with a 0, {0, y, -y}, which satisfy the power sum exactly when k is odd).
tests/test (lab/comprueba_lab.py) checks it against the O(p^2) enumeration of the paper's datos_P3d.py."""
import cmath
import itertools
import json
import math
import random

AZUL, NARANJA, MORADO, VERDE = '#1F6FB2', '#D55E00', '#7D3C98', '#117733'
TINTA, SUAVE, PAPEL, GRIS = '#333333', '#8a8a8a', '#fcfcfb', '#EDEFF1'


# ------------------------------------------------------------------------------------------------- arithmetic
def primes(lo, hi):
    if hi < 2:
        return []
    crib = [True] * (hi + 1)
    crib[0] = crib[1] = False
    for i in range(2, int(hi ** 0.5) + 1):
        if crib[i]:
            for j in range(i * i, hi + 1, i):
                crib[j] = False
    return [n for n in range(max(2, lo), hi + 1) if crib[n]]


_S = {0: {(0, 0): 3}, 1: {}, 2: {(1, 0): -2}, 3: {(0, 1): 3}}


def s_poly(k):
    """s_k = x^k + y^k + z^k as a polynomial in e2, e3 (e1 = 0): {(a, b): c} for c e2^a e3^b.
    The recursion of the paper's datos_P3d.py: s_k = -e2 s_{k-2} + e3 s_{k-3}."""
    for j in range(4, k + 1):
        if j in _S:
            continue
        out = {}
        for (a, b), c in _S[j - 2].items():
            out[(a + 1, b)] = out.get((a + 1, b), 0) - c
        for (a, b), c in _S[j - 3].items():
            out[(a, b + 1)] = out.get((a, b + 1), 0) + c
        _S[j] = {m: c for m, c in out.items() if c}
    return _S[k]


def Qk(k):
    """Q_k(u), u = e2^3/e3^2: s_k with its factors e2 and e3 removed, primitive, leading coefficient positive.
    Coefficients from the highest power of u down; [1] when s_k is a monomial (deg Q_k = 0)."""
    s = s_poly(k)
    a0, b0 = min(a for a, b in s), min(b for a, b in s)
    coef = {}
    for (a, b), c in s.items():
        a, b = a - a0, b - b0
        if a % 3 or b % 2:
            raise ValueError('s_%d is not homogeneous in u' % k)
        coef[a // 3] = coef.get(a // 3, 0) + c
    d = max(coef)
    cs = [coef.get(i, 0) for i in range(d, -1, -1)]
    g = 0
    for c in cs:
        g = math.gcd(g, abs(c))
    cs = [c // g for c in cs]
    if cs[0] < 0:
        cs = [-c for c in cs]
    return cs, a0, b0          # a0 > 0: e2 divides s_k; b0 > 0: e3 divides s_k


def deg_formula(k):
    return k // 6 - (1 if k % 6 == 1 else 0)


def dim_modular(w):
    """dim M_w(SL_2(Z)) for even w >= 0."""
    if w % 2 or w < 0:
        return 0
    return w // 12 if w % 12 == 2 else w // 12 + 1


def values_n3(k, p):
    """6 C_k(3,p)/(p-1), exactly (an integer), in O(p)."""
    pw = [pow(x, k, p) for x in range(p)]
    c = 0
    for y in range(p):
        z = (-1 - y) % p
        if y == 1 or z == 1 or y == z:
            continue
        if (1 + pw[y] + pw[z]) % p == 0:
            c += 1
    return c + (k % 2)


def count_subsets(k, n, p):
    """C_k(n,p) = #{T in F_p, |T| = n, sum t = sum t^k = 0}, by enumeration: n-1 elements, the last one is forced."""
    pw = [pow(x, k, p) for x in range(p)]
    c = 0
    for comb in itertools.combinations(range(p), n - 1):
        d = (-sum(comb)) % p
        if d <= comb[-1]:
            continue
        if (sum(pw[x] for x in comb) + pw[d]) % p == 0:
            c += 1
    return c


def artin_tate(k, n):
    """Theorem 8: {3,4,6} for k = 3, {3,4} for k = 5, {3} for every other k."""
    if k == 3:
        return n in (3, 4, 6)
    if k == 5:
        return n in (3, 4)
    return n == 3


def partitions(n, maxp=None):
    if maxp is None:
        maxp = n
    if n == 0:
        yield ()
        return
    for j in range(min(n, maxp), 0, -1):
        for rest in partitions(n - j, j):
            yield (j,) + rest


def singular_points(weights, m, stop_at=None):
    """#{z in mu_m^4 / scaling : sum w_i z_i = 0} (z_0 = 1): the singular points of V_lambda (Lemma 1)."""
    root = [cmath.exp(2j * math.pi * e / m) for e in range(m)]
    w0 = weights[0]
    c = 0
    for exps in itertools.product(range(m), repeat=len(weights) - 1):
        s = w0 + sum(w * root[e] for w, e in zip(weights[1:], exps))
        if abs(s) < 1e-9:
            c += 1
            if stop_at and c >= stop_at:
                return c
    return c


def S_m(m, nmax):
    """The n in 3..nmax with every length-four stratum singular (n = 3 has none: vacuously in)."""
    out = []
    for n in range(3, nmax + 1):
        if all(singular_points(lam, m, stop_at=1) > 0 for lam in partitions(n) if len(lam) == 4):
            out.append(n)
    return out


def a_p(p):
    """Frobenius trace of E: y^2 = x^3 + x^2 - x (conductor 20)."""
    c = 0
    for x in range(p):
        r = (x * x * x + x * x - x) % p
        if r == 0:
            c += 1
        elif pow(r, (p - 1) // 2, p) == 1:
            c += 2
    return p - c


def roots_mod(coefs, p):
    """Roots in F_p of sum coefs[i] Y^(len-1-i)."""
    out = []
    for y in range(p):
        v = 0
        for c in coefs:
            v = (v * y + c) % p
        if v == 0:
            out.append(y)
    return out


# ------------------------------------------------------------------------------------------------- drawing
def esc(s):
    return str(s).replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


class Ax:
    """A rectangle of an svg with data coordinates: x0..x1 → left..right, y0..y1 → bottom..top (ylog: log10)."""

    def __init__(self, left, top, width, height, x0, x1, y0, y1, ylog=False):
        self.l, self.t, self.w, self.h = left, top, width, height
        self.x0, self.x1, self.ylog = x0, x1, ylog
        self.y0, self.y1 = (math.log10(y0), math.log10(y1)) if ylog else (y0, y1)
        self.o = []

    def X(self, x):
        return self.l + (x - self.x0) / float(self.x1 - self.x0) * self.w

    def Y(self, y):
        if self.ylog:
            y = math.log10(max(y, 1e-300))
        return self.t + self.h - (y - self.y0) / float(self.y1 - self.y0) * self.h

    def inside(self, y):
        v = math.log10(y) if (self.ylog and y > 0) else y
        return (not self.ylog or y > 0) and self.y0 <= v <= self.y1

    def frame(self, xticks, yticks, xlabel='', ylabel='', xfmt=str, yfmt=str):
        o = self.o
        o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s"/>' % (
            self.l, self.t + self.h, self.l + self.w, self.t + self.h, SUAVE))
        o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s"/>' % (
            self.l, self.t, self.l, self.t + self.h, SUAVE))
        for x in xticks:
            o.append('<text x="%.1f" y="%.1f" font-size="10" text-anchor="middle" fill="%s">%s</text>' % (
                self.X(x), self.t + self.h + 13, TINTA, esc(xfmt(x))))
        for y in yticks:
            o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#E8EBEE"/>' % (
                self.l, self.Y(y), self.l + self.w, self.Y(y)))
            o.append('<text x="%.1f" y="%.1f" font-size="10" text-anchor="end" fill="%s">%s</text>' % (
                self.l - 4, self.Y(y) + 3, TINTA, esc(yfmt(y))))
        if xlabel:
            o.append('<text x="%.1f" y="%.1f" font-size="11" text-anchor="middle" fill="%s">%s</text>' % (
                self.l + self.w / 2, self.t + self.h + 28, TINTA, esc(xlabel)))
        if ylabel:
            o.append('<text x="%.1f" y="%.1f" font-size="11" text-anchor="middle" fill="%s" transform="rotate(-90 %.1f %.1f)">%s</text>' % (
                self.l - 38, self.t + self.h / 2, TINTA, self.l - 38, self.t + self.h / 2, esc(ylabel)))

    def line(self, pts, color, width=1.6, dash=''):
        pts = [(x, y) for x, y in pts if self.inside(y)]
        if len(pts) > 1:
            self.o.append('<polyline fill="none" stroke="%s" stroke-width="%s"%s points="%s"/>' % (
                color, width, ' stroke-dasharray="%s"' % dash if dash else '',
                ' '.join('%.1f,%.1f' % (self.X(x), self.Y(y)) for x, y in pts)))

    def dot(self, x, y, r, fill, stroke=PAPEL, title=''):
        self.o.append('<circle cx="%.1f" cy="%.1f" r="%.1f" fill="%s" stroke="%s">%s</circle>' % (
            self.X(x), self.Y(y), r, fill, stroke, '<title>%s</title>' % esc(title) if title else ''))

    def text(self, x, y, s, color=TINTA, size=10, anchor='start'):
        self.o.append('<text x="%.1f" y="%.1f" font-size="%s" text-anchor="%s" fill="%s">%s</text>' % (
            self.X(x), self.Y(y), size, anchor, color, esc(s)))


def svg(width, height, parts, title=''):
    head = ('<svg viewBox="0 0 %d %d" style="max-width:100%%;background:%s" xmlns="http://www.w3.org/2000/svg" '
            'font-family="sans-serif">' % (width, height, PAPEL))
    t = ('<text x="%d" y="16" font-size="12.5" text-anchor="middle" fill="%s">%s</text>' % (width / 2, TINTA, esc(title))
         if title else '')
    return head + t + ''.join(parts) + '</svg>'


def num(p, key, default, lo, hi):
    try:
        v = int(str(p.get(key, default)).strip())
    except ValueError:
        v = default
    return max(lo, min(hi, v))


def fail(msg):
    return json.dumps({'error': msg})


# ------------------------------------------------------------------------------------------------- Figure 1
def run_grid(params):
    p = json.loads(params)
    kmax, nmax = num(p, 'kmax', 12, 3, 30), num(p, 'nmax', 12, 3, 24)
    k, n = num(p, 'k', 5, 3, 30), num(p, 'n', 4, 3, 6)
    pmax = num(p, 'pmax', 41, 5, 200)
    KS, NS = list(range(3, kmax + 1)), list(range(3, nmax + 1))
    c = 26
    W, H = 70 + c * len(NS) + 20, 40 + c * len(KS) + 50
    o = []
    for i, kk in enumerate(KS):
        y = 30 + c * (len(KS) - 1 - i)
        o.append('<text x="60" y="%d" font-size="10" text-anchor="end" fill="%s">%d</text>' % (y + c / 2 + 3, TINTA, kk))
        for j, nn in enumerate(NS):
            x = 66 + c * j
            if not artin_tate(kk, nn):
                fc, ec, txt, tc, what = GRIS, GRIS, '', TINTA, 'not Artin–Tate'
            elif nn > 3 or Qk(kk)[0] == [1]:
                fc, ec, txt, tc, what = VERDE, VERDE, 'AT', 'white', 'Artin–Tate, quadratic characters'
            elif kk in (6, 9):
                fc, ec, txt, tc, what = '#CFE6CD', MORADO, 'S₃', MORADO, 'nonabelian, group exactly S₃ (the paper, k = 6, 9)'
            elif kk <= 12:
                fc, ec, txt, tc, what = '#E8F2E7', '#A9C9A6', 'n.a.', '#5E7F5C', (
                    'nonabelian, group larger than S₃ (the paper: S₃×C₂ at k = 8, 10, 11; not determined at k = 12)')
            else:
                fc, ec, txt, tc, what = '#F3F7F2', '#A9C9A6', 'n.a.', '#5E7F5C', (
                    'Artin–Tate, not quadratic (deg Q_k > 0); the paper names the group only for k ≤ 12')
            mark = ' stroke-width="2.6"' if (kk, nn) == (k, n) else ''
            o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s" stroke="%s"%s><title>k = %d, n = %d: %s</title></rect>'
                     % (x, y, c - 3, c - 3, fc, TINTA if mark else ec, mark, kk, nn, what))
            if txt:
                o.append('<text x="%.1f" y="%.1f" font-size="8.5" font-weight="bold" text-anchor="middle" fill="%s">%s</text>'
                         % (x + (c - 3) / 2.0, y + (c - 3) / 2.0 + 3, tc, txt))
    for j, nn in enumerate(NS):
        o.append('<text x="%.1f" y="%d" font-size="10" text-anchor="middle" fill="%s">%d</text>' % (
            66 + c * j + (c - 3) / 2.0, 30 + c * len(KS) + 12, TINTA, nn))
    o.append('<text x="%.1f" y="%d" font-size="11" text-anchor="middle" fill="%s">n (size of the subset)</text>' % (
        66 + c * len(NS) / 2.0, 30 + c * len(KS) + 28, TINTA))
    o.append('<text x="14" y="%d" font-size="11" fill="%s" transform="rotate(-90 14 %d)">k</text>' % (
        30 + c * len(KS) / 2, TINTA, 30 + c * len(KS) / 2))
    extra = sum(1 for kk in KS for nn in NS if nn > 3 and artin_tate(kk, nn))
    fig = svg(W, H, o, 'Live cells for k ≤ %d, n ≤ %d: the column n = 3 and %d more' % (kmax, nmax, extra))
    # the counts of one cell, enumerated
    if n - 1 > 4:
        return fail('n ≤ 5 for the enumeration')
    budget = 3_000_000
    rows, used = [], 0
    for q in primes(5, pmax):
        if k % q == 0:
            continue
        cost = math.comb(q, n - 1)
        if used + cost > budget:
            break
        used += cost
        cnt = count_subsets(k, n, q)
        rows.append([q, cnt, '%.4f' % (cnt / float(q - 1))])
    live = artin_tate(k, n)
    text = ('Cell (k, n) = (%d, %d): %s by Theorem 8. The table lists C_%d(%d, p), every %d-subset of F_p counted, '
            'for the primes p ≤ %d (p ∤ k)%s. The counts are data to look at; the verdict on the cell is the theorem, '
            'not these numbers.' % (k, n, 'Artin–Tate' if live else 'not Artin–Tate', k, n, n, rows[-1][0] if rows else 0,
                                    ' (stopped where the enumeration would be too long in a browser)'
                                    if rows and rows[-1][0] < max(primes(5, pmax)) else ''))
    import moments_3d
    return json.dumps({'text': text,
                       'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-1'}, moments_3d.grid3d(kmax, nmax)],
                       'table': {'head': ['p', 'C_%d(%d, p)' % (k, n), 'C/(p−1)'], 'rows': rows}})


def random_grid():
    return json.dumps({'kmax': str(random.randint(8, 24)), 'nmax': str(random.randint(6, 16)),
                       'k': str(random.choice([3, 4, 5, 6, 7])), 'n': str(random.choice([3, 4])),
                       'pmax': str(random.choice([31, 41, 61, 97]))})


# ------------------------------------------------------------------------------------------------- Figure 3
def run_collapse(params):
    p = json.loads(params)
    mmax, nmax = num(p, 'mmax', 24, 1, 30), num(p, 'nmax', 10, 4, 12)
    predicted = {1: [3], 3: [3], 2: [3, 4, 6], 6: [3, 4, 5, 6]}
    col = {1: SUAVE, 2: AZUL, 3: MORADO, 6: NARANJA}
    rows, bad = [], []
    for m in range(1, mmax + 1):
        s = S_m(m, nmax)
        g = math.gcd(m, 6)
        ok = s == predicted[g]
        if not ok:
            bad.append(m)
        rows.append([m, m + 1, g, '{%s}' % ', '.join(map(str, s)), '✓' if ok else '✗ (Theorem 4: {%s})'
                     % ', '.join(map(str, predicted[g]))])
    W = 640
    cell = min(24, (W - 40) / float(mmax))
    o = []
    for i, row in enumerate(rows):
        m, g = row[0], row[2]
        x = 20 + i * cell
        o.append('<rect x="%.1f" y="34" width="%.1f" height="%.1f" fill="white" stroke="%s" stroke-width="1.3">'
                 '<title>m = %d (k = %d): S_m = %s</title></rect>' % (x, cell - 3, cell - 3, col[g], m, m + 1, row[3]))
        o.append('<text x="%.1f" y="%.1f" font-size="9" text-anchor="middle" fill="%s">%d</text>' % (
            x + (cell - 3) / 2, 34 + (cell - 3) / 2 + 3, col[g], m))
    pos = {1: 90, 3: 240, 2: 400, 6: 550}
    for g in (1, 3, 2, 6):
        cx = pos[g]
        for i, row in enumerate(rows):
            if row[2] == g:
                o.append('<line x1="%.1f" y1="%.1f" x2="%d" y2="130" stroke="%s" stroke-opacity="0.35"/>' % (
                    20 + i * cell + (cell - 3) / 2, 34 + cell - 3, cx, col[g]))
        seen = sorted({r[3] for r in rows if r[2] == g})
        o.append('<rect x="%d" y="130" width="130" height="52" fill="%s" fill-opacity="0.16"/>' % (cx - 65, col[g]))
        o.append('<text x="%d" y="150" font-size="11" text-anchor="middle" fill="%s">gcd(m,6) = %d</text>' % (cx, col[g], g))
        o.append('<text x="%d" y="171" font-size="12" text-anchor="middle" fill="%s">%s</text>' % (
            cx, TINTA, esc(' or '.join(seen) if seen else '—')))
    o.append('<text x="165" y="205" font-size="10" text-anchor="middle" font-style="italic" fill="%s">gcd 1 and gcd 3: '
             'the same answer</text>' % TINTA)
    fig = svg(W, 215, o, '%d moduli m = k − 1, S_m computed from the definition, n ≤ %d' % (mmax, nmax))
    text = ('S_m = the n ≤ %d all of whose length-four strata V_λ are singular, found by searching μ_m⁴ for a point '
            'with Σ λ_i z_i = 0 (Lemma 1) for every partition λ of n into four parts. %s' % (
                nmax, 'Every m ≤ %d gives the set Theorem 4 predicts from gcd(m, 6) alone.' % mmax if not bad else
                'These m do NOT give the predicted set: %s.' % bad))
    return json.dumps({'text': text, 'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-3'},
                                                 __import__('moments_3d').collapse3d(rows, mmax)],
                       'table': {'head': ['m', 'k = m + 1', 'gcd(m, 6)', 'S_m (computed)', 'Theorem 4'], 'rows': rows}})


def random_collapse():
    return json.dumps({'mmax': str(random.randint(8, 24)), 'nmax': str(random.randint(7, 10))})


# ------------------------------------------------------------------------------------------------- Figure 4
def genus_n4(k):
    """The paper's genus of the normalisation of the stratum (1,1,1,1), the witness of n = 4."""
    if k % 2 == 0:
        return (k - 1) * (k - 2) // 2
    if k == 3:
        return 0          # the cubic is three lines: no residual curve
    return (k - 4) * (k - 5) // 2


def genus_n6(k):
    """The paper's genus of the normalisation of (3,1,1,1), the witness of n = 6: smooth for k even, one node for k odd."""
    return (k - 1) * (k - 2) // 2 - (1 if k % 2 else 0)


def run_genus(params):
    p = json.loads(params)
    kmax = num(p, 'kmax', 12, 4, 20)
    KS = list(range(3, kmax + 1))
    rows = []
    g4, g6 = [], []
    for k in KS:
        m = k - 1
        pa = (k - 1) * (k - 2) // 2
        n4, n6 = singular_points((1, 1, 1, 1), m), singular_points((3, 1, 1, 1), m)
        a, b = genus_n4(k), genus_n6(k)
        g4.append(a)
        g6.append(b)
        rows.append([k, pa, n4, pa - n4, a, n6, pa - n6, b])
    top = max(g6 + [1])
    W, H = 640, 260
    ax = Ax(56, 40, 560, 170, 2.4, kmax + 0.6, 0, top * 1.18)
    step = max(1, int(round(top / 6.0 / 5.0)) * 5) if top > 12 else 2
    ax.frame(KS, list(range(0, int(top * 1.18) + 1, step)), 'k', 'genus of the normalisation')
    for i, k in enumerate(KS):
        if g4[i] == 0 or g6[i] == 0:
            ax.o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" fill-opacity="0.10"/>' % (
                ax.X(k - 0.48), ax.Y(top * 1.18), ax.X(k + 0.48) - ax.X(k - 0.48), ax.Y(0) - ax.Y(top * 1.18), VERDE))
        for dx, g, cc, nm in ((-0.19, g4[i], AZUL, 'n = 4 witness (1,1,1,1)'), (0.19, g6[i], MORADO, 'n = 6 witness (3,1,1,1)')):
            x0, x1 = ax.X(k + dx - 0.17), ax.X(k + dx + 0.17)
            ax.o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s"><title>k = %d, %s: genus %d</title></rect>'
                        % (x0, ax.Y(g), x1 - x0, ax.Y(0) - ax.Y(g), cc, k, nm, g))
            ax.text(k + dx, g + top * 0.02, str(g), VERDE if g == 0 else cc, 8.5, 'middle')
    ax.o.append('<rect x="70" y="44" width="10" height="10" fill="%s"/><text x="85" y="53" font-size="10" fill="%s">'
                'witness at n = 4: λ = (1,1,1,1)</text>' % (AZUL, TINTA))
    ax.o.append('<rect x="70" y="60" width="10" height="10" fill="%s"/><text x="85" y="69" font-size="10" fill="%s">'
                'witness at n = 6: λ = (3,1,1,1)</text>' % (MORADO, TINTA))
    fig = svg(W, H, ax.o, 'Two witnesses, and the columns where one is rational')
    zeros = [k for i, k in enumerate(KS) if g4[i] == 0 or g6[i] == 0]
    differ = [k for k, r in zip(KS, rows) if r[3] != r[4]]
    text = ('The bars are the genera the paper gives (proof of Theorem 8). The table adds what can be counted here: the '
            'arithmetic genus (k−1)(k−2)/2 of a plane curve of degree k and its singular points, found in μ_(k−1)⁴ by '
            'Lemma 1. A node removes one unit of genus only on an irreducible curve: where «pa − #sing» and the genus '
            'differ (k = %s), the (1,1,1,1) curve is reducible — for odd k it is (x+y)(x+z)(y+z) times a residual curve. '
            'A witness of genus 0 appears only at k = %s.' % (', '.join(map(str, differ)) or '—', ', '.join(map(str, zeros))))
    return json.dumps({'text': text, 'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-4'},
                                                 __import__('moments_3d').genus3d(KS, g4, g6)],
                       'table': {'head': ['k', 'pa', '#sing (1,1,1,1)', 'pa − #sing', 'genus, n = 4',
                                          '#sing (3,1,1,1)', 'pa − #sing', 'genus, n = 6'], 'rows': rows}})


def random_genus():
    return json.dumps({'kmax': str(random.randint(6, 14))})


# ------------------------------------------------------------------------------------------------- Figure 5
def run_values(params):
    p = json.loads(params)
    kmin, kmax = num(p, 'kmin', 3, 3, 60), num(p, 'kmax', 14, 3, 60)
    pmax = num(p, 'pmax', 257, 7, 3000)
    if kmax < kmin:
        kmin, kmax = kmax, kmin
    if (kmax - kmin + 1) * pmax > 120000:
        return fail('too long for a browser: keep (number of k) × p_max ≤ 120000')
    PS = primes(5, pmax)
    KS = list(range(kmin, kmax + 1))
    V, rows, top = {}, [], 0
    for k in KS:
        d = {}
        for q in PS:
            if k % q == 0:
                continue
            d.setdefault(values_n3(k, q), []).append(q)
        V[k] = d
        top = max([top] + list(d))
        q, a0, b0 = Qk(k)
        rows.append([k, len(q) - 1, 'yes' if a0 else 'no', 'yes' if b0 else 'no',
                     ', '.join('%d (%d)' % (v, len(d[v])) for v in sorted(d))])
    ax = Ax(60, 40, 560, 190, kmin - 0.8, kmax + 0.8, -1, top + 1.5)
    ax.frame(KS if len(KS) <= 30 else KS[::2], sorted({v for d in V.values() for v in d}) if top <= 30 else
             list(range(0, top + 1, 6)), 'k', '6 C_k(3,p)/(p−1)')
    for k in KS:
        nprimes = float(sum(len(v) for v in V[k].values()))
        elem = Qk(k)[0] == [1]
        for val, ps in V[k].items():
            share = len(ps) / nprimes
            ax.dot(k, val, 3 + 13 * math.sqrt(share), VERDE if elem else AZUL,
                   title='k = %d: value %d on %d of %d primes' % (k, val, len(ps), int(nprimes)))
            if share < 0.22:
                ax.text(k + 0.28, val - 0.25, str(len(ps)), SUAVE, 8)
    ax.o.append('<circle cx="72" cy="48" r="6" fill="%s"/><text x="82" y="52" font-size="10" fill="%s">Q_k constant</text>'
                '<circle cx="182" cy="48" r="6" fill="%s"/><text x="192" y="52" font-size="10" fill="%s">Q_k has a root: '
                'a cubic decides</text>' % (VERDE, TINTA, AZUL, TINTA))
    fig = svg(640, 280, ax.o, 'Every value of the count on the %d primes 5 ≤ p ≤ %d, area = share of primes' % (len(PS), pmax))
    elem = [k for k in KS if Qk(k)[0] == [1]]
    text = ('Each disc is a value of 6 C_k(3,p)/(p−1), counted exactly for every prime 5 ≤ p ≤ %d (p ∤ k); its area is the '
            'share of primes that give it, and the rare ones carry their count. Q_k is constant here for k = %s '
            '(Theorem 12: exactly k ∈ {3, 4, 5, 7}); there the count is a quadratic character and takes at most two values. '
            'Elsewhere the values climb in steps of 6, one per root of Q_k whose cubic Y³ + uY − u splits.'
            % (pmax, ', '.join(map(str, elem)) or 'none'))
    return json.dumps({'text': text, 'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-5'},
                                                 __import__('moments_3d').values3d(KS, pmax)],
                       'table': {'head': ['k', 'deg Q_k', 'e₂ | s_k', 'e₃ | s_k', 'values (number of primes)'],
                                 'rows': rows}})


def random_values():
    a = random.randint(3, 30)
    return json.dumps({'kmin': str(a), 'kmax': str(a + random.randint(3, 12)), 'pmax': str(random.choice([150, 257, 400]))})


# ------------------------------------------------------------------------------------------------- Figure 6
def run_degree(params):
    p = json.loads(params)
    kmax = num(p, 'kmax', 60, 8, 200)
    KS = list(range(3, kmax + 1))
    G = {k: len(Qk(k)[0]) - 1 for k in KS}
    bad = [k for k in KS if G[k] != deg_formula(k)]
    badm = [k for k in KS if G[k] + 1 != dim_modular(2 * k)]
    top = max(G.values())
    ax = Ax(56, 40, 560, 190, 1.5, kmax + 3, -1.6, top + 1)
    tick = max(1, kmax // 12 // 5 * 5) if kmax > 60 else 6
    ax.frame(list(range(6, kmax + 1, tick)), list(range(0, top + 1, max(1, top // 6 // 2 * 2) or 1)), 'k', 'deg Q_k')
    ax.line([(3, 0.5), (kmax, kmax / 6.0)], SUAVE, 0.9)
    ax.text(kmax + 0.5, kmax / 6.0, 'k/6', SUAVE, 9)
    for k in KS:
        if G[k] == 0:
            ax.o.append('<circle cx="%.1f" cy="%.1f" r="7" fill="none" stroke="%s" stroke-width="1.8"/>' % (
                ax.X(k), ax.Y(0), VERDE))
            ax.text(k, -1.4, str(k), VERDE, 9, 'middle')
        if k % 6 == 1:
            ax.o.append('<rect x="%.1f" y="%.1f" width="7" height="7" fill="%s"><title>k = %d: deg %d</title></rect>' % (
                ax.X(k) - 3.5, ax.Y(G[k]) - 3.5, NARANJA, k, G[k]))
        else:
            ax.dot(k, G[k], 3, AZUL, title='k = %d: deg %d' % (k, G[k]))
    fig = svg(640, 280, ax.o, 'deg Q_k from s_k, for 3 ≤ k ≤ %d: six ladders of slope 1/6, one a step lower' % kmax)
    text = ('deg Q_k is read off s_k (its e₂ and e₃ factors removed), for every k ≤ %d. Against Proposition 15, '
            '⌊k/6⌋ − [k ≡ 1 mod 6]: %s. Against Proposition 16, deg Q_k + 1 = dim M_2k(SL₂(Z)): %s. Zero exactly at k = %s.'
            % (kmax, 'equal for every k' if not bad else 'DIFFERENT at k = %s' % bad,
               'equal for every k' if not badm else 'DIFFERENT at k = %s' % badm,
               ', '.join(str(k) for k in KS if G[k] == 0)))
    rows = [[k, G[k], deg_formula(k), dim_modular(2 * k), ' '.join(map(str, Qk(k)[0]))] for k in KS if k <= 24]
    return json.dumps({'text': text, 'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-6'},
                                                 __import__('moments_3d').degree3d(kmax)],
                       'table': {'head': ['k', 'deg Q_k (from s_k)', '⌊k/6⌋ − [k≡1]', 'dim M_2k',
                                          'Q_k (coefficients, highest power of u first; k ≤ 24)'], 'rows': rows}})


def random_degree():
    return json.dumps({'kmax': str(random.choice([30, 60, 90, 120, 150]))})


# ------------------------------------------------------------------------------------------------- Figure 7
def parse_cubic(text):
    try:
        cs = [int(x) for x in str(text).replace(',', ' ').split()]
    except ValueError:
        return None
    return cs if len(cs) == 4 and cs[0] != 0 else None


def run_primes(params):
    p = json.loads(params)
    pmax = num(p, 'pmax', 1200, 50, 4000)
    cs = parse_cubic(p.get('cubic', '2 0 3 -3'))
    if cs is None:
        return fail('the cubic: four integers a b c d for aY³ + bY² + cY + d, a ≠ 0')
    a, b, c, d = cs
    disc = b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d
    if disc == 0:
        return fail('the cubic has a repeated root (discriminant 0)')
    PS = [q for q in primes(7, pmax) if (6 * a * disc) % q]
    split = {q: len(roots_mod(cs, q)) == 3 for q in PS}
    dens = sum(split.values()) / float(len(PS))
    # is the split decided by p mod M on these primes? (each class seen at least twice, both outcomes never mixed)
    found = None
    for M in range(2, 121):
        classes = {}
        for q in PS:
            classes.setdefault(q % M, set()).add(split[q])
        counts = {}
        for q in PS:
            counts[q % M] = counts.get(q % M, 0) + 1
        if all(len(v) == 1 for v in classes.values()) and min(counts.values()) >= 2:
            found = M
            break
    QS = [q for q in primes(7, pmax) if q != 5]
    ys = [a_p(q) for q in QS]
    W, H = 640, 390
    o = []
    ax1 = Ax(40, 34, 580, 60, 0, pmax * 1.01, 0, 1)
    for q in PS:
        ax1.o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" stroke-width="%s"/>' % (
            ax1.X(q), ax1.Y(0), ax1.X(q), ax1.Y(1), MORADO if split[q] else '#E4E7EA', 1.3 if split[q] else 0.8))
    ax1.frame([0, pmax // 2, pmax], [], '')
    o += ax1.o
    o.append('<text x="40" y="128" font-size="10" fill="%s">purple: %s splits completely mod p (%.1f%% of %d primes)</text>'
             % (TINTA, esc(cubic_name(cs)), 100 * dens, len(PS)))
    ax2 = Ax(56, 160, 564, 190, 0, pmax * 1.01, -2.1 * math.sqrt(pmax), 2.1 * math.sqrt(pmax))
    r = int(2 * math.sqrt(pmax) // 20 * 20) or 10
    ax2.frame([0, pmax // 2, pmax], [-r, 0, r], 'p', 'a_p')
    xs = [7 + i * (pmax - 7) / 200.0 for i in range(201)]
    ax2.line([(x, 2 * math.sqrt(x)) for x in xs], NARANJA, 1)
    ax2.line([(x, -2 * math.sqrt(x)) for x in xs], NARANJA, 1)
    for q, y in zip(QS, ys):
        ax2.dot(q, y, 1.8, AZUL, AZUL)
    o += ax2.o
    o.append('<text x="56" y="152" font-size="10" fill="%s">k = 3, n = 5: a_p of y² = x³ + x² − x takes %d distinct values on '
             'these %d primes; orange: ±2√p</text>' % (TINTA, len(set(ys)), len(QS)))
    fig = svg(W, H, o, 'Two different failures of PORC, measured on the primes p ≤ %d' % pmax)
    text = ('Above: the primes where %s splits completely (discriminant %d). %s Below: the Frobenius traces a_p of the '
            'curve of conductor 20 behind C_3(5,p), with Hasse’s bound ±2√p: their number of distinct values keeps growing '
            'with p_max. The paper’s default cubic 2Y³ + 3Y − 3 is the one of C_6(3,p) (Proposition 11): its split density '
            'is 1/6 by Chebotarev (group S₃).' % (
                cubic_name(cs), disc,
                ('On these primes the split is decided by p mod %d — an abelian cubic does that.' % found) if found else
                ('No modulus M ≤ 120 decides the split on these primes (each class seen twice or more).')))
    return json.dumps({'text': text, 'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-7'},
                                                 __import__('moments_3d').primes3d(cs, pmax)],
                       'table': {'head': ['', 'value'], 'rows': [
                           ['primes used (above)', len(PS)], ['split completely', sum(split.values())],
                           ['density', '%.4f' % dens], ['modulus M ≤ 120 that decides the split', found or 'none'],
                           ['distinct a_p (below)', len(set(ys))]]}})


def cubic_name(cs):
    a, b, c, d = cs
    terms = []
    for coef, mon in ((a, 'Y³'), (b, 'Y²'), (c, 'Y'), (d, '')):
        if coef == 0:
            continue
        s = ('−' if coef < 0 else '+') + ' '
        v = abs(coef)
        s += (str(v) if (v != 1 or not mon) else '') + mon
        terms.append(s)
    out = ' '.join(terms)
    return out[2:] if out.startswith('+ ') else '−' + out[2:]


def random_primes():
    return json.dumps({'pmax': str(random.choice([600, 1200, 2000])),
                       'cubic': random.choice(['2 0 3 -3', '1 0 -3 1', '1 0 0 -2', '1 1 -2 -1'])})


# ------------------------------------------------------------------------------------------------- Figure 8
def run_circle(params):
    p = json.loads(params)
    k = num(p, 'k', 15, 6, 80)
    lo, hi = math.pi / 3, math.pi / 2

    def s_of(t):
        return (-2 * math.cos(t)) ** k + 2 * math.cos(k * t)

    def u_of(t):
        c2 = 4 * math.cos(t) ** 2
        return (1 - c2) ** 3 / c2

    nodes = [j * math.pi / k for j in range(int(math.ceil(k / 3.0)), k // 2 + 1)]
    pts = [lo + 1e-6] + [t for t in nodes if lo < t < hi] + [hi - 1e-6]
    roots = []
    for a, b in zip(pts, pts[1:]):
        if s_of(a) * s_of(b) < 0:
            for _ in range(90):
                mid = 0.5 * (a + b)
                if s_of(a) * s_of(mid) <= 0:
                    b = mid
                else:
                    a = mid
            roots.append(0.5 * (a + b))
    q, a0, b0 = Qk(k)
    deg = len(q) - 1
    us = [u_of(t) for t in roots]

    def Qval(u):
        v = 0.0
        for c in q:
            v = v * u + c
        return v

    resid = [abs(Qval(u)) / max(1.0, sum(abs(c) * u ** i for i, c in enumerate(reversed(q)))) for u in us]
    ts = [lo + (hi - lo) * i / 600.0 for i in range(1, 600)]
    sv = [s_of(t) for t in ts]
    m = max(abs(x) for x in sv) or 1.0
    ax1 = Ax(70, 34, 540, 140, lo, hi, -m * 1.1, m * 1.1)
    ax1.frame([], [0], '', 's_%d(θ)' % k, yfmt=lambda y: '0')
    for t in nodes:
        if lo < t < hi:
            ax1.o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#d6d6d6" stroke-dasharray="2 2"/>' % (
                ax1.X(t), ax1.Y(m * 1.1), ax1.X(t), ax1.Y(-m * 1.1)))
    ax1.line(list(zip(ts, sv)), AZUL, 1.6)
    for t in roots:
        ax1.dot(t, 0, 5, 'white', NARANJA, 'root θ = %.6f' % t)
    ylo, yhi = 1e-3, 1e3
    if us:
        ylo, yhi = min(ylo, min(us) / 10), max(yhi, max(us) * 10)
    ax2 = Ax(70, 200, 540, 150, lo, hi, ylo, yhi, ylog=True)
    decs = list(range(int(math.floor(math.log10(ylo))), int(math.ceil(math.log10(yhi))) + 1, 2))
    ax2.frame([lo, (lo + hi) / 2, hi], [10.0 ** e for e in decs], 'θ', 'u(θ), log scale',
              xfmt=lambda x: {lo: 'π/3', hi: 'π/2'}.get(x, '5π/12'), yfmt=lambda y: '1e%d' % round(math.log10(y)))
    ax2.line([(t, u_of(t)) for t in ts], VERDE, 1.8)
    for t, u in zip(roots, us):
        ax2.o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" stroke-dasharray="1.5 1.6"/>' % (
            ax2.X(t), ax2.Y(ylo), ax2.X(t), ax2.Y(u), NARANJA))
        ax2.dot(t, u, 5, 'white', NARANJA, 'u = %.6g' % u)
        ax2.text(t + 0.004, u * 2.2, 'u = %.4g' % u, NARANJA, 9)
    fig = svg(640, 395, ax1.o + ax2.o, 'Step one of Appendix A for k = %d, where deg Q_%d = %d' % (k, k, deg))
    agree = len(roots) == deg
    text = ('s_%d(θ) = (−2cos θ)^%d + 2cos(%dθ) on (π/3, π/2): %d sign change(s) between consecutive jπ/k, each a root; '
            'u(θ) = (1 − 4cos²θ)³/(4cos²θ) climbs from 0 to ∞, so each root lands on a distinct u > 0. '
            '%s Each u is checked as a root of Q_%d computed from s_%d (relative residual below %.0e).' % (
                k, k, k, len(roots), ('The count equals deg Q_%d = %d.' % (k, deg)) if agree else
                ('The count (%d) is NOT deg Q_%d = %d.' % (len(roots), k, deg)), k, k, max(resid + [0.0]) * 10 or 1e-12))
    rows = [[i + 1, '%.10f' % t, '%.8g' % u, '%.1e' % r] for i, (t, u, r) in enumerate(zip(roots, us, resid))]
    return json.dumps({'text': text, 'plots': [{'kind': 'svg', 'svg': fig, 'figure': 'paperfig-8'},
                                                 __import__('moments_3d').circle3d(k)],
                       'table': {'head': ['root', 'θ', 'u(θ)', '|Q_k(u)| (relative)'], 'rows': rows}})


def random_circle():
    return json.dumps({'k': str(random.randint(8, 60))})
