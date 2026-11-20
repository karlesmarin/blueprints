# encaje: ORQUESTACIÓN de los laboratorios del blueprint real-rational-integer: cada run_* recibe JSON y calcula en el navegador.
"""Labs of «Real, rational and integer sums of squares». Pure Python: every verdict is computed here, never assumed."""
import json
import math
import random
from fractions import Fraction as Fr

import labkit as K
import lengths_draw as D


def ival(p, k, d, lo, hi):
    try:
        v = int(str(p.get(k, d)).strip() or d)
    except ValueError:
        v = d
    return max(lo, min(hi, v))


def parse_edges(s, n):
    e = set()
    for tok in str(s).replace(',', ' ').split():
        a, b = tok.split('-')
        a, b = int(a) - 1, int(b) - 1
        if not (0 <= a < n and 0 <= b < n) or a == b:
            raise ValueError(tok)
        e.add((min(a, b), max(a, b)))
    return sorted(e)


def adjacency(n, edges):
    A = [[0.0] * n for _ in range(n)]
    for a, b in edges:
        A[a][b] = A[b][a] = 1.0
    return A


def jacobi(A):
    """Eigenvalues of a real symmetric matrix by Jacobi rotations."""
    n = len(A)
    M = [r[:] for r in A]
    for _ in range(100):
        off = sum(M[i][j]**2 for i in range(n) for j in range(n) if i != j)
        if off < 1e-22:
            break
        for p in range(n):
            for q in range(p + 1, n):
                if abs(M[p][q]) < 1e-15:
                    continue
                th = (M[q][q] - M[p][p]) / (2 * M[p][q])
                t = (1 if th >= 0 else -1) / (abs(th) + math.sqrt(th * th + 1))
                c = 1 / math.sqrt(t * t + 1)
                s = t * c
                for k in range(n):
                    a, b = M[k][p], M[k][q]
                    M[k][p], M[k][q] = c * a - s * b, s * a + c * b
                for k in range(n):
                    a, b = M[p][k], M[q][k]
                    M[p][k], M[q][k] = c * a - s * b, s * a + c * b
    return sorted((M[i][i] for i in range(n)), reverse=True)


def levels(vals):
    out = []
    for v in vals:
        if out and abs(out[-1][0] - v) < 1e-8:
            out[-1][1] += 1
        else:
            out.append([v, 1])
    return out


def real_length(n, edges):
    A = adjacency(n, edges)
    w = jacobi(A)
    rho = max(abs(x) for x in w) if n else 0
    esc = 2.0 if rho <= 2 + 1e-9 else rho
    lv = levels([x / esc for x in w])
    par = all(abs(abs(v) - 1) < 1e-8 or m % 2 == 0 for v, m in lv)
    return (n if par else n + 1), lv, esc


def components(n, edges):
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen, comps = set(), []
    for i in range(n):
        if i in seen:
            continue
        st, c = [i], []
        seen.add(i)
        while st:
            u = st.pop()
            c.append(u)
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        comps.append(c)
    return comps, adj


def run_real(params):
    p = json.loads(params)
    n = ival(p, 'n', 5, 1, 12)
    try:
        e = parse_edges(p.get('edges', ''), n)
    except ValueError as x:
        return K.error('Could not read the edge %s. Write edges as 1-2 2-3.' % x)
    r, lv, esc = real_length(n, e)
    note = '' if esc == 2 else ' The spectral radius exceeds 2, so here H = A/%.4f, not A/2.' % esc
    rows = [['%.6f' % v, m, 'free (±1)' if abs(abs(v) - 1) < 1e-8 else ('paired' if m % 2 == 0 else 'alone: costs the extra square')] for v, m in lv]
    return K.result('n = %d. Real length ℓ_R = %d (Theorem 3.1).%s' % (n, r, note), [D.graph(n, e, 'your graph'), D.ladder(lv, 'levels of H')],
                    K.table(['level', 'multiplicity', 'role'], rows))


def random_real():
    n = random.randint(3, 8)
    tipo = random.choice(['cycle', 'path', 'random'])
    if tipo == 'cycle':
        e = ['%d-%d' % (i + 1, (i + 1) % n + 1) for i in range(n)]
    elif tipo == 'path':
        e = ['%d-%d' % (i + 1, i + 2) for i in range(n - 1)]
    else:
        e = ['%d-%d' % (i + 1, j + 1) for i in range(n) for j in range(i + 1, n) if random.random() < .35]
    return json.dumps({'n': str(n), 'edges': ' '.join(e)})


def integer_length(n, edges):
    comps, adj = components(n, edges)
    if any(len(v) > 2 for v in adj.values()):
        return None, comps, adj
    caminos = sum(1 for c in comps if len(c) >= 2 and sum(len(adj[u]) for u in c) // 2 == len(c) - 1)
    aislados = sum(1 for c in comps if len(c) == 1)
    return n + caminos + aislados % 2, comps, adj


def run_integer(params):
    p = json.loads(params)
    n = ival(p, 'n', 5, 1, 12)
    try:
        e = parse_edges(p.get('edges', ''), n)
    except ValueError as x:
        return K.error('Could not read the edge %s. Write edges as 1-2 2-3.' % x)
    z, comps, adj = integer_length(n, e)
    r, lv, esc = real_length(n, e)
    if z is None:
        v = [i + 1 for i, a in adj.items() if len(a) > 2]
        txt = 'ℓ_Z = ∞: vertices %s have degree at least three (Theorem 4.1). Real length: %d.' % (v, r)
    else:
        txt = 'ℓ_Z = %d, against ℓ_R = %d (Theorem 4.1).' % (z, r)
    rows = [[' '.join(str(u + 1) for u in sorted(c)), len(c), max((len(adj[u]) for u in c), default=0)] for c in comps]
    vcol, ecol = {}, {}
    for c in comps:
        ciclo = len(c) >= 3 and all(len(adj[u]) == 2 for u in c)
        for u in c:
            vcol[u] = D.RO if len(adj[u]) > 2 else (D.AZ if ciclo else (D.GR if len(c) == 1 else D.NA))
    for a_, b_ in e:
        ecol[(a_, b_)] = D.RO if len(adj[a_]) > 2 or len(adj[b_]) > 2 else vcol[a_]
    return K.result(txt, [D.graph(n, e, 'your graph', vcol, ecol, leyenda=True)], K.table(['component', 'vertices', 'maximum degree'], rows))


def random_integer():
    n = random.randint(3, 9)
    e = []
    i = 1
    while i < n:
        k = random.randint(1, 4)
        j = min(n, i + k)
        e += ['%d-%d' % (a, a + 1) for a in range(i, j)]
        if j - i >= 2 and random.random() < .4:
            e.append('%d-%d' % (i, j))
        i = j + 1 + random.randint(0, 1)
    if random.random() < .3:
        e.append('1-%d' % n)
        e.append('1-%d' % max(2, n - 1))
    return json.dumps({'n': str(n), 'edges': ' '.join(e)})


def is_square(x):
    return x >= 0 and math.isqrt(x)**2 == x


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, math.isqrt(n) + 1))


def run_kn(params):
    p = json.loads(params)
    n = ival(p, 'n', 11, 3, 2001)
    if n % 2 == 0:
        return K.result('n = %d is even: −1/(n−1) has odd multiplicity, so ℓ_R = n + 1 already. Theorem 6.1 is about odd n.' % n)
    m = (n - 1) // 2
    a, b = is_square(n), is_square(n - 2)
    txt = 'n = %d, m = %d. ' % (n, m)
    txt += 'n is a square: ℓ_Q(H_n) = n.' if a else ('n − 2 = %d² is a square: ℓ_Q(H_n) = n.' % math.isqrt(n - 2) if b else 'Neither n nor n − 2 is a square: ℓ_Q(H_n) > n although ℓ_R(H_n) = n (Theorem 6.1).')
    rows = [['discriminant needed', 'n ≡ (n(n−2))^m modulo squares'], ['m parity', 'even' if m % 2 == 0 else 'odd'], ['n mod 8', n % 8]]
    if b and is_prime(n) and n % 4 == 3 and n <= 83:
        qr = {(x * x) % n for x in range(1, n)}
        s = math.isqrt(n - 2)
        N = [[0 if i == j else 1 + s * (1 if (j - i) % n in qr else -1) for j in range(n)] for i in range(n)]
        okT = all(sum(N[i][k] * N[j][k] for k in range(n)) == ((n - 1)**2 if i == j else 0) for i in range(n) for j in range(n))
        okS = all(N[i][j] + N[j][i] == (0 if i == j else 2) for i in range(n) for j in range(n))
        txt += ' Paley witness T = (J − I + %dS)/%d, checked here in exact arithmetic: orthogonal %s, symmetric part H_n %s.' % (s, n - 1, okT, okS)
    return K.result(txt, [D.strip(n, is_square, 'odd n up to 129; your n is ringed when it is in range')], K.table(['item', 'value'], rows))


def random_kn():
    return json.dumps({'n': str(random.choice([3, 5, 7, 9, 11, 13, 25, 27, 49, 51, 81, 83, 2 * random.randint(2, 60) + 1]))})


def val(a, p):
    a = Fr(a)
    v, x, d = 0, a.numerator, a.denominator
    while x % p == 0:
        x //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return v, Fr(x, d)


def hilbert(a, b, p):
    al, u = val(a, p)
    be, v = val(b, p)
    if p == 2:
        u = u.numerator * pow(u.denominator, -1, 8) % 8
        v = v.numerator * pow(v.denominator, -1, 8) % 8
        return -1 if (((u - 1) // 2) * ((v - 1) // 2) + al * ((v * v - 1) // 8) + be * ((u * u - 1) // 8)) % 2 else 1
    r = -1 if al % 2 and be % 2 and p % 4 == 3 else 1
    uu = u.numerator * pow(u.denominator, -1, p) % p
    vv = v.numerator * pow(v.denominator, -1, p) % p
    if be % 2 and pow(uu, (p - 1) // 2, p) != 1:
        r = -r
    if al % 2 and pow(vv, (p - 1) // 2, p) != 1:
        r = -r
    return r


def hasse(d, p):
    r = 1
    for i in range(len(d)):
        for j in range(i + 1, len(d)):
            r *= hilbert(d[i], d[j], p)
    return r


def square_p(a, p):
    v, u = val(a, p)
    if v % 2:
        return False
    if p == 2:
        return u.numerator * pow(u.denominator, -1, 8) % 8 == 1
    return pow(u.numerator * pow(u.denominator, -1, p) % p, (p - 1) // 2, p) == 1


def hyperbolic_p(d, p):
    m = len(d) // 2
    det = Fr(1)
    for x in d:
        det *= x
    return square_p((-1)**m * det, p) and hasse(d, p) == hasse([1, -1] * m, p)


def squarefree(a):
    a = Fr(a)
    x = a.numerator * a.denominator
    s, r, k = (1 if x > 0 else -1), 1, 2
    x = abs(x)
    while k * k <= x:
        e = 0
        while x % k == 0:
            x //= k
            e += 1
        if e % 2:
            r *= k
        k += 1
    return s * r * x


def primes_of(a):
    out, x, k = set(), abs(a), 2
    while k * k <= x:
        while x % k == 0:
            out.add(k)
            x //= k
        k += 1
    if x > 1:
        out.add(x)
    return out


def run_local(params):
    p = json.loads(params)
    try:
        lam = Fr(str(p.get('lam', '1/2')))
        d = [Fr(x) for x in str(p.get('form', '2 6')).replace(',', ' ').split()]
    except (ValueError, ZeroDivisionError):
        return K.error('Write λ as a fraction and the form as a list of positive rationals.')
    if not abs(lam) < 1 or not d or any(x <= 0 for x in d):
        return K.error('Need |λ| < 1 and a positive diagonal form.')
    delta = 1 - lam * lam
    rows = [['δ = 1 − λ²', str(delta)], ['L', 'Q(√%d)' % squarefree(-delta)], ['dimension', len(d)]]
    giro = D.rotation(lam, delta, 'the rotation of this level')
    if len(d) % 2:
        return K.result('Odd dimension: never hyperbolic over L. No rational rotation of cosine λ fills this space.', [giro, D.primes([('dimension %d is odd' % len(d), 'bad')], 'the test')], K.table(['item', 'value'], rows))
    m = len(d) // 2
    det = Fr(1)
    for x in d:
        det *= x
    sd, nd = squarefree((-1)**m * det), squarefree(-delta)
    rows.append(['signed discriminant', sd])
    if sd not in (1, nd):
        return K.result('Fails: the signed discriminant %d is not in {1, %d} modulo squares.' % (sd, nd), [giro, D.primes([('discriminant %d not in {1, %d}' % (sd, nd), 'bad')], 'the test')], K.table(['item', 'value'], rows))
    ps = {2}
    for x in d + [delta]:
        ps |= primes_of(x.numerator) | primes_of(x.denominator)
    marcas = [('discriminant %d is in {1, %d}' % (sd, nd), 'ok')]
    for q in sorted(ps):
        sp = square_p(-delta, q)
        hp = hyperbolic_p(d, q) if sp else None
        rows.append(['p = %d' % q, 'L splits at p; form %s' % ('hyperbolic' if hp else 'NOT hyperbolic') if sp else 'L is a field at p: no condition'])
        marcas.append(('p = %d: %s' % (q, ('hyperbolic' if hp else 'not hyperbolic') if sp else 'L is a field here: no condition'), ('ok' if hp else 'bad') if sp else 'free'))
        if sp and not hp:
            return K.result('Fails at p = %d.' % q, [giro, D.primes(marcas, 'the test')], K.table(['item', 'value'], rows))
    return K.result('The form becomes hyperbolic over L: rational rotations of cosine %s fill this space (Theorem 5.1).' % lam, [giro, D.primes(marcas, 'the test')], K.table(['item', 'value'], rows))


def random_local():
    den = random.choice([2, 3, 4, 5, 8, 10])
    num = random.randint(0, den - 1) * random.choice([1, -1])
    c = 1 - Fr(num, den)**2
    a, b = random.randint(1, 5), random.randint(1, 5)
    forma = [a, a * c, b, b * c] if random.random() < .6 else [random.randint(1, 7) for _ in range(random.choice([2, 3, 4]))]
    return json.dumps({'lam': str(Fr(num, den)), 'form': ' '.join(str(x) for x in forma)})


def run_weight(params):
    p = json.loads(params)
    try:
        a = max(-1.0, min(1.0, float(str(p.get('a', '0.5')))))
    except ValueError:
        return K.error('Write a as a number between −1 and 1.')
    n = ival(p, 'n', 5, 3, 10)
    A = [[0.0] * n for _ in range(n)]
    for i in range(n - 1):
        A[i][i + 1] = A[i + 1][i] = 1.0
    A[0][n - 1] = A[n - 1][0] = a
    w = jacobi(A)
    lv = levels([x / 2 for x in w])
    par = all(abs(abs(v) - 1) < 1e-8 or m % 2 == 0 for v, m in lv)
    r = n if par else n + 1
    c = math.sqrt(max(0.0, 1 - a * a))
    return K.result('a = %.4f, n = %d: real length %d. Added form has coefficient %.6f (Proposition 3.3).' % (a, n, r, c),
                    [D.bond(n, a, 'the ring, last bond of weight a'), D.semicircle(a, 'coefficient of the added form')],
                    K.table(['level of H_a', 'multiplicity'], [['%.6f' % v, m] for v, m in lv]))


def random_weight():
    return json.dumps({'a': random.choice(['1', '-1', '0', '%.3f' % random.uniform(-1, 1)]), 'n': str(random.randint(3, 9))})


# ---------------------------------------------------------------- Theorem thm:scalar (21-nov): λ I_m, with a 3D view
NIVEL = {1: 1, 2: 2, 3: 2, 4: 4}          # the level s of L = Q(√−δ) as a function of τ(δ) (Lemma lem:level)


def tau(c):
    """Number of rational squares needed for the positive rational c (Lagrange, Legendre, sums of two squares)."""
    n = squarefree(c)
    if n == 1:
        return 1
    if all(p % 4 != 3 for p in primes_of(n)):
        return 2
    return 4 if n % 8 == 7 else 3


def scalar_numbers(m, t):
    s = NIVEL[t]
    rho = m % (2 * s)
    return m + min((-m) % (2 * s), t), min(rho, 2 * s - rho)


def run_scalar(params):
    p = json.loads(params)
    try:
        lam = Fr(str(p.get('lam', '3/4')))
        mmax = int(p.get('mmax', '16'))
    except (ValueError, ZeroDivisionError):
        return K.error('Write λ as a fraction, for example 3/4, and the largest m as an integer.')
    if not abs(lam) < 1:
        return K.error('Need |λ| < 1.')
    if not 1 <= mmax <= 40:
        return K.error('Choose 1 ≤ m ≤ 40.')
    delta = 1 - lam * lam
    t = tau(delta)
    s = NIVEL[t]
    rows = []
    for m in range(1, mmax + 1):
        lq, dq = scalar_numbers(m, t)
        rows.append([m, lq, lq - m, dq])
    ms = list(range(1, mmax + 1))
    items = []
    for tt in (1, 2, 3, 4):
        pts = [[m, tt, scalar_numbers(m, tt)[0] - m] for m in ms]
        if tt == t:
            items.append(K.points3(pts, name='your λ: τ = %d' % tt, star=True, size=7, opacity=1.0))
            items.append(K.curve3(pts, name='', width=3))
        else:
            items.append(K.points3(pts, name='τ = %d' % tt, size=4, opacity=0.35))
    vista = K.three_d(items, title='excess ℓ_Q(λI_m) − m against m and τ(1 − λ²)', axes=('m', 'τ', 'excess'))
    texto = ('δ = 1 − λ² = %s needs τ = %d rational square%s, so L = Q(√%d) has level s = %d. By the theorem the excess '
             'ℓ_Q(λI_m) − m = min((−m) mod 2s, τ) depends only on m mod 2s = %d, is at most 4, and repeats with period exactly '
             '2s. The highlighted series is yours; the faint ones are the other three values of τ.'
             % (delta, t, '' if t == 1 else 's', squarefree(-delta), s, 2 * s))
    return K.result(texto, [vista], K.table(['m', 'ℓ_Q(λI_m)', 'excess', 'defect d_Q'], rows))


def random_scalar():
    a = random.randint(1, 15)
    b = random.randint(a + 1, 16)
    return json.dumps({'lam': '%d/%d' % (a, b), 'mmax': str(random.choice([8, 12, 16]))})
