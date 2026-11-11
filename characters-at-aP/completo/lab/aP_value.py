# encaje: laboratorio del blueprint de characters-at-aP (Cor. 6.1, Thms 7.1 y 10.1); corre en el navegador con Pyodide
# (Lemmario). Porta el laboratorio del Teorema A del blueprint viejo (note_prasad2/blueprint/lab/lab_A.py) sin evlib.py.
"""Lab of Corollary 6.1, Theorem 7.1 and Theorem 10.1: the character of Sp(2m) at a power of Kostant's a_P.

Everything is exact integer arithmetic. Two independent routes to the same number:
  * the paper's formulas: the capacity rule (Cor. 6.1), the signed root quotient (-1)^E Z_q(l)/Z_q(rho) (Thm 7.1) and
    the factorisation kappa * prod of dimensions (Thm 10.1);
  * the character itself, as the symplectic Jacobi-Trudi determinant 1/2 det(h_{lam_i-i+j} + h_{lam_i-i-j+2}) with the
    integer h_n of the alphabet of a_P^k, H(z) = (1-z)^2/(1-z^q)^d (d even) or (1-z^2)/(1-z^q)^d (d odd) (Prop. 4.1).
"""
from fractions import Fraction
from math import comb, gcd
import json


def roots_vals(x):
    """(x, alpha) over the positive roots e_i - e_j, e_i + e_j (i < j) and 2 e_i of C_m, with their names."""
    m = len(x)
    out = []
    for i in range(m):
        for j in range(i + 1, m):
            out.append(('e%d-e%d' % (i + 1, j + 1), x[i] - x[j]))
            out.append(('e%d+e%d' % (i + 1, j + 1), x[i] + x[j]))
        out.append(('2e%d' % (i + 1), 2 * x[i]))
    return out


def hseq(d, q, N):
    base = [0] * (N + 1)
    for j in range(N // q + 1):
        base[j * q] = comb(j + d - 1, d - 1)
    num = [1, -2, 1] if d % 2 == 0 else [1, 0, -1]
    h = [0] * (N + 1)
    for i, c in enumerate(num):
        for n in range(N + 1 - i):
            h[n + i] += c * base[n]
    return h


def det(M):
    M = [[Fraction(x) for x in r] for r in M]
    n, s = len(M), Fraction(1)
    for c in range(n):
        piv = next((r for r in range(c, n) if M[r][c] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            s = -s
        s *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for cc in range(c, n):
                M[r][cc] -= f * M[c][cc]
    return s


def character(lam, d, q):
    """The character value, exactly, by the symplectic Jacobi-Trudi determinant (Koike-Terada)."""
    m = len(lam)
    N = 2 * max(lam + [0]) + 2 * m + 4
    h = hseq(d, q, N)
    H = lambda n: h[n] if 0 <= n <= N else 0
    M = [[H(lam[i] - (i + 1) + (j + 1)) + H(lam[i] - (i + 1) - (j + 1) + 2) for j in range(m)] for i in range(m)]
    v = det(M) / 2
    assert v.denominator == 1
    return int(v)


def dim_gl(nu):
    n, num, den = len(nu), 1, 1
    for i in range(n):
        for j in range(i + 1, n):
            num *= nu[i] - nu[j] + j - i
            den *= j - i
    return Fraction(num, den)


def dim_bc(nu, half):
    """Weyl dimension of Sp_2n (half = 0) or SO_{2n+1} (half = 1/2) with highest weight nu."""
    n = len(nu)
    rho = [Fraction(n - i) - half for i in range(n)]   # (n, ..., 1) for Sp_2n; (n-1/2, ..., 1/2) for SO_2n+1
    l = [nu[i] + rho[i] for i in range(n)]
    v = Fraction(1)
    for i in range(n):
        for j in range(i + 1, n):
            v *= (l[i] ** 2 - l[j] ** 2) / (rho[i] ** 2 - rho[j] ** 2)
        v *= l[i] / rho[i]
    return v


def run(params):
    p_ = json.loads(params)
    try:
        m, k = int(p_.get('m', 3)), int(p_.get('k', 2))
        lam = [int(x) for x in str(p_.get('lam', '')).replace(';', ',').replace(' ', ',').split(',') if x.strip()]
    except ValueError:
        return json.dumps({'error': 'm and k must be integers, λ a list of integers such as 3,2,1'})
    t = 2 * m + 2
    if not 1 <= m <= 8:
        return json.dumps({'error': 'm must be between 1 and 8'})
    if not 1 <= k < t:
        return json.dumps({'error': 'k must be between 1 and %d (= 2m+1)' % (t - 1)})
    if len(lam) > m:
        return json.dumps({'error': 'λ has at most m = %d parts' % m})
    lam = (lam + [0] * m)[:m]
    if any(lam[i] < lam[i + 1] for i in range(m - 1)) or lam[-1] < 0 or max(lam) > 30:
        return json.dumps({'error': 'λ must be a partition (weakly decreasing, ≥ 0, entries ≤ 30)'})
    d = gcd(k, t)
    q, p = t // d, k // d
    rho = list(range(m, 0, -1))
    ell = [lam[i] + rho[i] for i in range(m)]
    RL, RR = roots_vals(ell), roots_vals(rho)
    NL = sum(1 for _, v in RL if v % q == 0)
    NR = sum(1 for _, v in RR if v % q == 0)
    chi = character(lam, d, q)
    # folded classes and capacities (Corollary 6.1)
    classes = {}
    for x in ell:
        r = x % q
        classes.setdefault(min(r, (q - r) % q), []).append(x)
    rows, over = [], False
    for c in range(q // 2 + 1):
        fixed = (2 * c) % q == 0
        cap = d // 2 if fixed else d
        occ = len(classes.get(c, []))
        over = over or occ > cap
        state = 'over capacity' if occ > cap else ('one place free' if occ == cap - 1 and d % 2 == 0 else '')
        rows.append([str(c) + (' (fixed)' if fixed else ''), str(cap), str(occ),
                     ', '.join(str(x) for x in classes.get(c, [])) or '—', state])
    lines = ['m = %d, k = %d: t = 2m+2 = %d, d = gcd(k, t) = %d, q = t/d = %d, p = k/d = %d.' % (m, k, t, d, q, p),
             'λ = (%s), ℓ = λ+ρ = (%s).' % (', '.join(map(str, lam)), ', '.join(map(str, ell))),
             'Theorem 3.1: N_q(ℓ) = %d against r_q = N_q(ρ) = %d, so the character is %s.'
             % (NL, NR, 'non-zero' if NL == NR else 'zero'),
             'Corollary 6.1: %s.' % ('some class is over capacity' if over else 'no class is over capacity')]
    if NL == NR:
        ZL = 1
        for _, v in RL:
            if v % q == 0:
                ZL *= v
        ZR = 1
        for _, v in RR:
            if v % q == 0:
                ZR *= v
        E = sum(p * a // q - p * b // q for (_, a), (_, b) in zip(RL, RR))
        formula = (-1) ** E * Fraction(ZL, ZR)
        lines.append('Theorem 7.1: (−1)^E · Z_q(ℓ)/Z_q(ρ) = (−1)^%d · %d/%d = %s.' % (E, ZL, ZR, formula))
        # Theorem 10.1: the modulus as kappa times a product of dimensions
        D, factors = Fraction(1), []
        for c, xs in sorted(classes.items()):
            n = len(xs)
            if (2 * c) % q:
                eps_l = [x if (x - c) % q == 0 else -x for x in xs]
                y = sorted(((v - c) // q for v in eps_l), reverse=True)
                nu = [y[i] - y[-1] - (n - 1 - i) for i in range(n)]
                dc, name = dim_gl(nu), 'GL_%d' % n
            elif c == 0:
                xs_ = sorted(xs, reverse=True)
                nu = [xs_[i] // q - (n - i) for i in range(n)]
                dc, name = dim_bc(nu, 0), 'Sp_%d' % (2 * n)
            else:
                xs_ = sorted(xs, reverse=True)
                nu = [int(Fraction(xs_[i], q) - (n - 1 - i) - Fraction(1, 2)) for i in range(n)]
                dc, name = dim_bc(nu, Fraction(1, 2)), 'SO_%d' % (2 * n + 1)
            D *= dc
            factors.append('dim %s(%s) = %s' % (name, ','.join(map(str, nu)), dc))
        if d % 2:
            kappa = 1
        else:
            free = [c for c in range(q // 2 + 1)
                    if len(classes.get(c, [])) == ((d // 2) if (2 * c) % q == 0 else d) - 1]
            kappa = 1 if free == [0] else 2
        lines.append('Theorem 10.1: κ = %d and %s, so |χ| = %s.' % (kappa, '; '.join(factors) or 'no factor', kappa * D))
        sign = 1 if chi > 0 else -1
        lines.append('The character itself (Jacobi–Trudi determinant, exact integers): χ_λ(a_P^%d) = %d. Value %s, sign %s, '
                     'factorisation %s.' % (k, chi, 'agrees' if formula == chi else 'DISAGREES',
                                           'agrees' if (formula > 0) == (sign > 0) else 'DISAGREES',
                                           'agrees' if kappa * D == abs(chi) else 'DISAGREES'))
        lines.insert(3, 'The %d vanishing factors: of ℓ, %s; of ρ, %s.'
                     % (NL, ', '.join('(ℓ,%s) = %d' % (nm, a) for nm, a in RL if a % q == 0) or 'none',
                        ', '.join('(ρ,%s) = %d' % (nm, b) for nm, b in RR if b % q == 0) or 'none'))
    else:
        lines.append('The character itself (Jacobi–Trudi determinant, exact integers): χ_λ(a_P^%d) = %d.' % (k, chi))
    res = {'text': '<br>'.join(lines),
           'table': {'head': ['folded class mod q', 'capacity', 'occupancy', 'entries ℓ_i', ''], 'rows': rows}}
    return json.dumps(res)


if __name__ == '__main__':
    # self-check: every weight of a box, m <= 4, every k: formula, sign and factorisation against the determinant
    bad = n = 0
    for m in range(1, 5):
        for k in range(1, 2 * m + 2):
            import itertools
            for lam in itertools.product(range(7), repeat=m):
                if any(lam[i] < lam[i + 1] for i in range(m - 1)):
                    continue
                r = json.loads(run(json.dumps({'m': m, 'k': k, 'lam': ','.join(map(str, lam))})))
                n += 1
                if 'DISAGREES' in r['text'] or 'error' in r:
                    bad += 1
                    print('BAD', m, k, lam, r)
    print('weights checked:', n, 'disagreements:', bad)
    print(run(json.dumps({'m': 5, 'k': 4, 'lam': '3,2,1'})))
