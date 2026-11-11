# encaje: laboratorio de characters-at-aP, v2 (8-nov): k módulo t, fórmulas con MathJax, cajas de capacidad y mapa de supervivientes
"""Lab of Corollary 6.1, Theorems 3.1, 7.1 and 10.1, v2 (8-nov-2026, Carles: «el lab no funciona bien … faltan
gráficos que representen bien el paper»). The arithmetic is aP_value's (unchanged, self-checked on 2 639 weights);
here: any k ≥ 1 (reduced modulo t = 2m+2; k ≡ 0 is the identity, where χ is the dimension), the formulas typeset, and
two figures: the capacity boxes of the reader's weight (Figure 2 / Proposition 6.2) and the survivors around it, with
their sign and |χ| (Figures 3 and 4)."""
import json
import math
from fractions import Fraction
from math import gcd

import labkit as K
import aP_figs as F
from aP_value import roots_vals, character, dim_gl, dim_bc


def parse(p_):
    m, k = int(p_.get('m', 3)), int(p_.get('k', 2))
    lam = [int(x) for x in str(p_.get('lam', '')).replace(';', ',').replace(' ', ',').split(',') if x.strip()]
    return m, k, lam


def value(lam, m, d, q, p):
    """χ_λ(a_P^k) by Theorems 3.1 and 7.1 (no determinant): 0, or (−1)^E Z_q(ℓ)/Z_q(ρ)."""
    rho = list(range(m, 0, -1))
    ell = [lam[i] + rho[i] for i in range(m)]
    RL, RR = roots_vals(ell), roots_vals(rho)
    if sum(1 for _, v in RL if v % q == 0) != sum(1 for _, v in RR if v % q == 0):
        return 0
    ZL = ZR = 1
    for _, v in RL:
        if v % q == 0:
            ZL *= v
    for _, v in RR:
        if v % q == 0:
            ZR *= v
    E = sum(p * a // q - p * b // q for (_, a), (_, b) in zip(RL, RR))
    return (-1) ** E * Fraction(ZL, ZR)


def survivors_map(lam, m, d, q, p):
    """The weights (λ1, λ2, λ3..λm fixed as the reader's) in a box, as points sized by |χ| and coloured by sign."""
    N = min(20, 5 * -(-max(10, lam[0] + 3) // 5))   # múltiplo de 5: marcas enteras en los ejes (8-nov)
    pos, neg, zer, me = ([], [], []), ([], [], []), ([], []), ([], [])
    rest = lam[2:] if m >= 2 else []
    low = rest[0] if rest else 0
    for a in range(low, N + 1):
        for b in (range(low, a + 1) if m >= 2 else [0]):
            l = ([a, b] + rest) if m >= 2 else [a]
            v = value(l, m, d, q, p)
            x, y = (a, b) if m >= 2 else (a, float(v))
            if v == 0:
                zer[0].append(x); zer[1].append(y)
            else:
                tgt = pos if v > 0 else neg
                tgt[0].append(x); tgt[1].append(y); tgt[2].append(min(9.0, 1.6 + 1.2 * math.log2(1 + abs(float(v)))))
    series = [{'name': 'χ > 0 (size: |χ|)', 'x': pos[0], 'y': pos[1], 'size': pos[2], 'color': '#1B6F8C'},
              {'name': 'χ < 0', 'x': neg[0], 'y': neg[1], 'size': neg[2], 'color': '#B5530F'},
              {'name': 'χ = 0 (a class over capacity)', 'x': zer[0], 'y': zer[1], 'size': 1.6, 'color': '#9E9E9E'}]
    you = (lam[0], lam[1]) if m >= 2 else (lam[0], float(value(lam, m, d, q, p)))
    series.append({'name': 'your λ', 'x': [you[0]], 'y': [you[1]], 'size': 6, 'color': '#C62828'})
    if m >= 2:
        # dos puntos invisibles fijan el recuadro [0, N]² (svg_plot toma el rango de los datos)
        series.append({'name': '', 'x': [0, N], 'y': [0, N], 'size': 0, 'color': '#ffffff'})
        fixed = (' with λ3..λm = (%s)' % ', '.join(map(str, rest))) if rest else ''
        title = 'Sp(%d) at a_P^%d: the survivors in the plane (λ1, λ2)%s' % (2 * m, p * (2 * m + 2) // q, fixed)
        return K.svg_plot(series, title=title, xlabel='λ1', ylabel='λ2', legend_below=True)
    return K.svg_plot(series, title='Sp(2) at the power: χ against λ1', xlabel='λ1', ylabel='χ', legend_below=True)


def survivors_3d(lam, m, d, q, p):
    """8-nov (Carles: «lo ideal es hacer uno en 2D con otro 3D»): the survivors in 3D. For m ≥ 3, the cloud
    (λ1, λ2, λ3) with λ4.. fixed as the reader's, as Figures 3 and 4 of the paper (Sp(6)); for m = 2, the value χ as
    the height over the plane (λ1, λ2). Blue χ > 0, orange χ < 0, the size grows with |χ|; the reader's λ is a star."""
    if m < 2:
        return None
    N = min(14, max(8, lam[0] + 2))
    groups = {}
    pts_you = []
    if m >= 3:
        rest = lam[3:]
        low = rest[0] if rest else 0
        for a in range(low, N + 1):
            for b in range(low, a + 1):
                for c in range(low, b + 1):
                    v = value([a, b, c] + rest, m, d, q, p)
                    if v:
                        k = (v > 0, min(3, int(math.log2(1 + abs(float(v))) // 2)))
                        groups.setdefault(k, []).append([a, b, c])
        pts_you = [lam[:3]]
        axes, title = ('λ1', 'λ2', 'λ3'), 'Sp(%d): the surviving weights in (λ1, λ2, λ3)%s' % (
            2 * m, (' with λ4.. = (%s)' % ', '.join(map(str, lam[3:]))) if lam[3:] else '')
    else:
        for a in range(0, N + 1):
            for b in range(0, a + 1):
                v = value([a, b], m, d, q, p)
                if v:
                    k = (v > 0, min(3, int(math.log2(1 + abs(float(v))) // 2)))
                    groups.setdefault(k, []).append([a, b, float(v)])
        pts_you = [[lam[0], lam[1], float(value(lam, m, d, q, p))]]
        axes, title = ('λ1', 'λ2', 'χ'), 'Sp(4): the value χ as a height over (λ1, λ2)'
    items = []
    for (pos, k), pts in sorted(groups.items()):
        items.append(K.points3(pts, name='%s, |χ| ~ 4^%d' % ('χ > 0' if pos else 'χ < 0', k),
                               color='#1B6F8C' if pos else '#B5530F', size=3 + 2 * k, opacity=0.75))
    items.append(K.points3(pts_you, name='your λ', color='#C62828', size=12, star=True, opacity=1))
    return K.three_d(items, title=title, axes=axes)


def run(params):
    try:
        m, k, lam = parse(json.loads(params))
    except ValueError:
        return K.error('m and k must be integers, λ a list of integers such as 3,2,1')
    t = 2 * m + 2
    if not 1 <= m <= 8:
        return K.error('m must be between 1 and 8')
    if k < 1:
        return K.error('k must be at least 1')
    if len(lam) > m:
        return K.error('λ has at most m = %d parts' % m)
    lam = (lam + [0] * m)[:m]
    if any(lam[i] < lam[i + 1] for i in range(m - 1)) or lam[-1] < 0 or max(lam) > 30:
        return K.error('λ must be a partition (weakly decreasing, ≥ 0, entries ≤ 30)')
    lines = []
    if k % t == 0:  # a_P has order t: the identity, where the character is the dimension
        D = dim_bc(lam, 0)
        return K.result('\\(k = %d\\) is a multiple of \\(t = 2m+2 = %d\\), the order of \\(a_P\\): \\(a_P^{\\,k} = 1\\) and '
                        '\\(\\chi_\\lambda(1) = \\dim = %s\\).' % (k, t, D))
    if k >= t:
        lines.append('\\(a_P\\) has order \\(t = %d\\), so \\(a_P^{\\,%d} = a_P^{\\,%d}\\).' % (t, k, k % t))
        k = k % t
    d = gcd(k, t)
    q, p = t // d, k // d
    rho = list(range(m, 0, -1))
    ell = [lam[i] + rho[i] for i in range(m)]
    RL, RR = roots_vals(ell), roots_vals(rho)
    NL = sum(1 for _, v in RL if v % q == 0)
    NR = sum(1 for _, v in RR if v % q == 0)
    chi = character(lam, d, q)
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
    lines += ['\\(m = %d,\\ k = %d\\): \\(t = 2m+2 = %d\\), \\(d = \\gcd(k,t) = %d\\), \\(q = t/d = %d\\), \\(p = k/d = %d\\).'
              % (m, k, t, d, q, p),
              '\\(\\lambda = (%s)\\), \\(\\ell = \\lambda+\\rho = (%s)\\).' % (', '.join(map(str, lam)), ', '.join(map(str, ell))),
              '<b>Theorem 3.1:</b> \\(N_q(\\ell) = %d\\) against \\(r_q = N_q(\\rho) = %d\\), so the character is <b>%s</b>.'
              % (NL, NR, 'non-zero' if NL == NR else 'zero'),
              '<b>Corollary 6.1:</b> %s (the boxes below).' % ('a class is over capacity' if over else 'no class is over capacity')]
    if NL == NR:
        formula = value(lam, m, d, q, p)
        ZL = ZR = 1
        for _, v in RL:
            if v % q == 0:
                ZL *= v
        for _, v in RR:
            if v % q == 0:
                ZR *= v
        E = sum(p * a // q - p * b // q for (_, a), (_, b) in zip(RL, RR))
        lines.append('<b>Theorem 7.1:</b> \\((-1)^{E}\\,Z_q(\\ell)/Z_q(\\rho) = (-1)^{%d}\\cdot %d/%d = %s\\).'
                     % (E, ZL, ZR, formula))
        D, factors = Fraction(1), []
        for c, xs in sorted(classes.items()):
            n = len(xs)
            if (2 * c) % q:
                eps_l = [x if (x - c) % q == 0 else -x for x in xs]
                y = sorted(((v - c) // q for v in eps_l), reverse=True)
                nu = [y[i] - y[-1] - (n - 1 - i) for i in range(n)]
                dc, name = dim_gl(nu), '\\mathrm{GL}_{%d}' % n
            elif c == 0:
                xs_ = sorted(xs, reverse=True)
                nu = [xs_[i] // q - (n - i) for i in range(n)]
                dc, name = dim_bc(nu, 0), '\\mathrm{Sp}_{%d}' % (2 * n)
            else:
                xs_ = sorted(xs, reverse=True)
                nu = [int(Fraction(xs_[i], q) - (n - 1 - i) - Fraction(1, 2)) for i in range(n)]
                dc, name = dim_bc(nu, Fraction(1, 2)), '\\mathrm{SO}_{%d}' % (2 * n + 1)
            D *= dc
            factors.append('\\dim %s(%s) = %s' % (name, ','.join(map(str, nu)), dc))
        if d % 2:
            kappa = 1
        else:
            free = [c for c in range(q // 2 + 1) if len(classes.get(c, [])) == ((d // 2) if (2 * c) % q == 0 else d) - 1]
            kappa = 1 if free == [0] else 2
        # una línea por factor: a 390 px la lista en una sola fórmula se salía (8-nov)
        lines.append('<b>Theorem 10.1:</b> \\(\\kappa = %d\\), one dimension per folded class:<br>%s<br>so \\(|\\chi| = %s\\).'
                     % (kappa, '<br>'.join('&nbsp;&nbsp;\\(%s\\)' % f for f in factors) or 'no factor', kappa * D))
        ok = formula == chi and kappa * D == abs(chi)
        lines.append('<b>The character itself</b> (symplectic Jacobi–Trudi determinant with the alphabet of Proposition 4.1, '
                     'exact integers): \\(\\chi_\\lambda(a_P^{\\,%d}) = %d\\). %s' % (
                         k, chi, 'Value, sign and factorisation agree.' if ok else '<b>DISAGREES</b>.'))
    else:
        lines.append('<b>The character itself</b> (Jacobi–Trudi, exact): \\(\\chi_\\lambda(a_P^{\\,%d}) = %d\\).' % (k, chi))
    plots = [F.boxes(classes, q, d, 'The folded classes mod %d and their capacities (Corollary 6.1; * = fixed class)' % q),
             survivors_map(lam, m, d, q, p)]
    tres = survivors_3d(lam, m, d, q, p)
    if tres:
        plots.append(tres)
    return K.result('<br>'.join(lines), plots,
                    K.table(['folded class mod q', 'capacity', 'occupancy', 'entries ℓ_i', ''], rows))


def random_run():
    import random
    m = random.randint(2, 5)
    k = random.randint(1, 2 * m + 1)
    lam = sorted((random.randint(0, 8) for _ in range(m)), reverse=True)
    return json.dumps({'m': str(m), 'k': str(k), 'lam': ','.join(map(str, lam))})


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    for m, k, lam in [(5, 4, '3,2,1'), (3, 2, '15,14,0'), (3, 9, '2,1'), (3, 8, '2,1'), (1, 1, '0'), (6, 7, '1,1,1,1'),
                      (2, 2, '1,0'), (3, 1, '2,1,0')]:
        r = json.loads(run(json.dumps({'m': str(m), 'k': str(k), 'lam': lam})))
        print(m, k, lam, '|', (r.get('error') or r['text'])[-140:].replace('<br>', ' / '), '| figuras', len(r.get('plots', [])))
