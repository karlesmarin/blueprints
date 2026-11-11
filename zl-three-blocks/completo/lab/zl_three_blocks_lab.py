# encaje: ORQUESTACIÓN de los laboratorios del blueprint zl-three-blocks: cada run_* recibe los parámetros (JSON), calcula con zl_core, dibuja con zl_draw y sustituye una figura del paper (2, 4, 5, 6, 7) por su versión viva con 2D + 3D; parámetros con nombre para enlazar desde el paper (?lab=<nodo>&n=…)
"""Labs of «Why three blocks?». Every verdict printed here is computed in the browser by the literal checker of
Definition 2.1 (zl_core.check), never assumed."""
import json
import random
from fractions import Fraction
from math import comb

import zl_core as Z
import zl_draw as G
from zl_data import F4_EXACT, F4_FAMILIES, RHO_CERT, TABLE, TENSOR, W22


def ok(probs):
    return 'admissible ✓ (checked here, cell by cell, against (C2) and (C3))' if not probs else \
        'NOT admissible: %d problem(s)' % len(probs)


def fr(q):
    return str(q) if q.denominator != 1 else str(q.numerator)


def ival(p, k, d, lo, hi):
    try:
        v = int(str(p.get(k, d)).strip() or d)
    except ValueError:
        v = d
    return max(lo, min(hi, v))


def out(text, plots, fig=None):
    """Every plot goes to the paper's figure it redraws (``fig`` for those that name none), each in its own panel in
    order (a, b, c…): the live figure shows its 2D and 3D views in place, so what the inputs or the die change is seen
    in the figure itself (29-oct, Carles: in Figure 6 «no se ve nada de forma aleatoria»: the staircase and the 3D views
    were only inside the lab, and the table, the only panel in place, does not depend on m)."""
    count = {}
    for p in plots:
        if fig and not p.get('figure'):
            p['figure'] = fig
        if p.get('figure'):
            k = count.get(p['figure'], 0)
            p['panel'] = 'abcdefgh'[k]
            count[p['figure']] = k + 1
    return json.dumps({'text': text, 'plots': plots})


# ------------------------------------------------------------------ Figure 2: the definition, on your own grid
def parse_rows(s, n):
    rows = []
    for part in s.replace(';', ' ').split():
        cols = [int(ch) for ch in part.replace(',', '') if ch.isdigit()]
        if not cols or any(not 1 <= c <= n for c in cols):
            raise ValueError(part)
        rows.append(sorted(set(c - 1 for c in cols)))
    return rows


def parse_pairs(s):
    pairs = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        nums = [int(t) for t in part.replace('(', ' ').replace(')', ' ').replace('-', ' ').replace(',', ' ').split()]
        if len(nums) != 4:
            raise ValueError(part)
        pairs.append(((nums[0] - 1, nums[1] - 1), (nums[2] - 1, nums[3] - 1)))
    return pairs


def distance(O, a, b):
    """Distance from a to b in R_O (opposite corners of a rectangle with four corners in O); 4 means ≥ 4."""
    def nb(c):
        return {d for d in O if d[0] != c[0] and d[1] != c[1] and (c[0], d[1]) in O and (d[0], c[1]) in O}
    seen, front = {a}, {a}
    for k in range(1, 4):
        front = set().union(*(nb(c) for c in front)) - seen if front else set()
        if b in front:
            return k
        seen |= front
    return 4


def run_definition(params):
    p = json.loads(params)
    n = ival(p, 'n', 3, 2, 8)
    try:
        rows = parse_rows(p.get('base', '12 13 23 1'), n)
        E2 = parse_pairs(p.get('pairs', '4,2-4,3'))
    except ValueError as e:
        return out('Could not read %s. Base: one row per word, its columns as digits (e.g. «12 13 23 1»). Pairs: '
                   '«row,col-row,col» separated by «;».' % e, [])
    m = len(rows)
    E1 = {(i, j) for i, r in enumerate(rows) for j in r}
    probs = Z.check(E1, E2, m, n)
    O = E1 | {c for pr in E2 for c in pr}
    c4 = Z.c4_free(E1)
    z = Z.z_value(m, n)
    base = ('C₄-free, |E₁| = %d' % len(E1)) if c4 else 'NOT C₄-free (a rectangle of four base cells)'
    if z is not None:
        base += ' = z(%d,%d) = m + C(n,2): a maximum base' % (m, n) if len(E1) == z and c4 else \
            ' (z(%d,%d) = %d: the base is not maximum, so this is not a configuration of z_L)' % (m, n, z)
    marks, lines = [], []
    def cell1(c):
        return '(row %d, column %d)' % (c[0] + 1, c[1] + 1)
    for t, why, det in probs:
        if isinstance(det, tuple) and len(det) == 2 and isinstance(det[0], int):
            shown = cell1(det)
        elif isinstance(det, tuple) and len(det) == 2:
            shown = ' and '.join(cell1(c) for c in det)
        else:
            shown = str(det)
        lines.append('pair %d: %s %s' % (t + 1, why, shown))
        if why.startswith('(C3)'):
            (i, j), (q0, q1) = E2[t][0], E2[t][1]
            k, l = det
            marks += [(k, l), (k, j), (k, q1), (i, l), (q0, l)]
        if why.startswith('(C2)'):
            marks += list(det)
    dists = ['pair %d: distance %s in R_O' % (t + 1, '≥ 3' if distance(O, a, b) >= 3 else distance(O, a, b))
             for t, (a, b) in enumerate(E2)]
    total = len(E1) + len(E2) if not probs else None
    text = ('%d × %d grid. Base: %s. Pairs: %s. %s. %s%s' % (
        m, n, base, len(E2), ok(probs), '; '.join(lines) + ('. ' if lines else ''), '; '.join(dists) + '.') +
        (' |E₁| + |E₂| = %d.' % total if total is not None and c4 and z is not None and len(E1) == z else ''))
    grid = G.grid_svg(m, n, E1, E2, bad={t for t, _, _ in probs}, marks=marks, transpose=False,
                      title='your configuration: base grey, pairs numbered, witnesses ringed in red')
    # 3D: the cells of O on the floor, the rectangles of R_O as arches, each pair as a tall dashed arch
    items = [{'type': 'points', 'points': [[c[1], c[0], 0] for c in E1], 'color': G.GREY, 'size': 7, 'name': 'base E₁'}]
    edges = set()
    Ol = sorted(O)
    for a in Ol:
        for b in Ol:
            if a < b and a[0] != b[0] and a[1] != b[1] and (a[0], b[1]) in O and (b[0], a[1]) in O:
                edges.add((a, b))
    for k, (a, b) in enumerate(sorted(edges)):
        items.append({'type': 'curve', 'points': G.arc3((a[1], a[0]), (b[1], b[0]), 0.6), 'color': '#9aa5b1', 'width': 1.5,
                      'name': 'R_O: opposite corners of a full rectangle' if k == 0 else ''})
    for t, (a, b) in enumerate(E2):
        col = G.RED if any(q == t for q, _, _ in probs) else '#B5530F'
        items.append({'type': 'points', 'points': [[a[1], a[0], 0], [b[1], b[0], 0]], 'color': col, 'size': 9,
                      'marker': 'star', 'name': 'pair %d' % (t + 1)})
        items.append({'type': 'curve', 'points': G.arc3((a[1], a[0]), (b[1], b[0]), 1.6), 'color': col, 'dash': True,
                      'width': 2.5, 'name': ''})
    return out(text, [{'kind': 'svg', 'svg': grid, 'title': 'Definition 2.1 on your grid', 'figure': 'paperfig-2'},
                      {'kind': '3d', 'title': 'the graph R_O: a pair is admissible iff its two cells are at distance ≥ 3',
                       'axes': ['column', 'row', ''], 'items': items, 'max_width': 900}], fig='paperfig-2')


# ------------------------------------------------------------------ Figure 4: build your own hollow triangle
def run_blocks(params):
    p = json.loads(params)
    if str(p.get('source', 'module')).strip().lower().startswith('paper'):
        return run_paper_22x5()
    n = ival(p, 'n', 5, 3, 12)
    x, y, z = ival(p, 'x', 0, 0, 12), ival(p, 'y', 0, 0, 12), ival(p, 'z', 0, 0, 12)
    if x + y + z != n or min(x, y, z) < 1:
        x, y, z = Z.balanced(n)
        note = 'block sizes (%d, %d, %d): the balanced split of n = %d (sizes must be ≥ 1 and add up to n)' % (x, y, z, n)
    else:
        note = 'block sizes (%d, %d, %d)' % (x, y, z)
    x, y, z = sorted((x, y, z), reverse=True)
    copies = ival(p, 'copies', 2, 1, 4)
    m, n, E1, E2, corner, rows, blocks = Z.configuration(x, y, z, copies)
    probs = Z.check(E1, E2, m, n)
    M, regime = Z.M_value(x, y, z)
    R, P = len(rows), len(E2) // copies
    lam = Z.lam(n)
    bal = Z.balanced(n)
    which = {}
    for b, cols in zip('ABC', blocks):
        for c in cols:
            which[c] = b
    text = ('n = %d, %s. One module: R = %d rows, P = %d pairs, P/R = %s = M(%d,%d,%d) (Proposition 6.3, regime %d). '
            'λ_%d = %s%s. With %d module(s) and the %d bare special rows: m = %d rows, |E₂| = %d pairs, %s; the base '
            'is maximum (|E₁| = %d = m + C(n,2), C₄-free: %s). Pairs per row overall: %d/%d = %.3f, tending to %s as '
            'modules are added. Corners: %d angles at A, %d at B, %d at C.' % (
                n, note, R, P, fr(M), x, y, z, regime, n, fr(lam),
                '' if M == lam else ' > M: the split (%d,%d,%d) is not balanced; the balanced one is %s' % (x, y, z, bal),
                copies, comb(n, 2), m, len(E2), ok(probs), len(E1), Z.c4_free(E1), len(E2), m, len(E2) / m, fr(M),
                corner.count('A'), corner.count('B'), corner.count('C')))
    # the grid shows ONE module (the special rows are bare: no pair touches them), so that it stays readable for n = 12
    sp = comb(n, 2)
    E1m = {(r - sp, c) for (r, c) in E1 if sp <= r < sp + R}
    keep = [t for t, (u, v) in enumerate(E2) if sp <= u[0] < sp + R]
    E2m = [((E2[t][0][0] - sp, E2[t][0][1]), (E2[t][1][0] - sp, E2[t][1][1])) for t in keep]
    grid = G.grid_svg(R, n, E1m, E2m, colour_of_pair=lambda t: G.CORNER[corner[keep[t]]],
                      col_colour=lambda c: G.BLOCK[which[c]], bad={keep.index(t) for t, _, _ in probs if t in keep},
                      title='one module, %d rows (the %d special rows are bare); pairs coloured by the corner of their angle'
                      % (R, sp), max_rows=70)
    # 3D: columns grouped in blocks (gaps between blocks), rows going back; pairs as arches over the floor
    gap = {c: c + 0.8 * 'ABC'.index(which[c]) for c in range(n)}
    special = comb(n, 2)
    wid = n + 1.6
    sy = G.row_scale(m, wid)
    fixed = [{'type': 'points', 'points': [[gap[c], r * sy, 0] for (r, c) in E1 if r < special], 'color': '#9e9e9e',
              'size': 4, 'name': 'special rows (bare)'}]
    slides = []
    for k in range(copies):
        lo, hi = special + k * R, special + (k + 1) * R
        its = [{'type': 'points', 'points': [[gap[c], r * sy, 0] for (r, c) in E1 if lo <= r < hi], 'color': G.GREY,
                'size': 5, 'name': 'base cell of each row' if k == 0 else ''}]
        for b in 'ABC':
            pts = [[gap[c], r * sy, 0] for t, (u, v) in enumerate(E2) for (r, c) in (u, v) if lo <= r < hi and which[c] == b]
            its.append({'type': 'points', 'points': pts, 'color': G.BLOCK[b], 'size': 5,
                        'name': 'endpoints in block %s' % b if k == 0 else ''})
        for cor in 'ABC':
            first = True
            for t, (u, v) in enumerate(E2):
                if corner[t] == cor and lo <= u[0] < hi:
                    h = wid * (0.25 + 0.35 * abs(u[1] - v[1]) / n)
                    its.append({'type': 'curve', 'points': G.arc3((gap[u[1]], u[0] * sy), (gap[v[1]], v[0] * sy), h),
                                'color': G.CORNER[cor], 'width': 1.6,
                                'name': ('angle at %s' % cor) if (k == 0 and first) else ''})
                    first = False
        slides.append(its)
    td = {'kind': '3d', 'title': 'the hollow triangle at work: arches = pairs, colour = the corner of their angle',
          'axes': ['column (blocks A | B | C)', 'row', ''], 'items': fixed, 'max_width': 1000,
          'slider': {'label': 'modules', 'values': list(range(1, copies + 1)), 'items': slides, 'cumulative': True}}
    groups = []
    for typ in ('AB', 'AC', 'BC'):
        cnt = sum(1 for r in rows if r[0] == typ)
        if cnt:
            groups.append((typ, cnt))
    tpl = G.template_svg((x, y, z), groups, fr(M))
    return out(text, [{'kind': 'svg', 'svg': tpl, 'title': 'Figure 3 (right) for your blocks', 'figure': 'paperfig-3'},
                      {'kind': 'svg', 'svg': grid, 'title': 'your three-block configuration', 'figure': 'paperfig-4'}, td], fig='paperfig-4')


def run_paper_22x5():
    E1 = {(i - 1, j - 1) for i, j in W22['E1']}
    E2 = [((a[0] - 1, a[1] - 1), (b[0] - 1, b[1] - 1)) for a, b in W22['E2']]
    probs = Z.check(E1, E2, 22, 5)
    blk = {0: 'A', 1: 'A', 2: 'B', 3: 'B', 4: 'C'}
    avoided = W22['avoided']

    def corner(t):
        (a, b) = E2[t]
        return ({'A', 'B', 'C'} - {avoided[a[0]], avoided[b[0]]}).pop() if avoided[a[0]] != avoided[b[0]] else 'A'
    text = ('The configuration of Figure 4 (22 × 5, blocks A = {1,2}, B = {3,4}, C = {5}): |E₁| = %d, |E₂| = %d, %s; '
            '20/78 > 1/4 pairs per free cell. Here the special rows also carry endpoints (16 of the 40).'
            % (len(E1), len(E2), ok(probs)))
    grid = G.grid_svg(22, 5, E1, E2, colour_of_pair=lambda t: G.CORNER[corner(t)], col_colour=lambda c: G.BLOCK[blk[c]],
                      row_labels=['%d%s' % (r + 1, avoided[r]) for r in range(22)],
                      title='Figure 4 (rows labelled with the block they avoid), checked here')
    gap = {c: c + 0.8 * 'ABC'.index(blk[c]) for c in range(5)}
    sy = G.row_scale(22, 6.6)
    items = [{'type': 'points', 'points': [[gap[c], r * sy, 0] for (r, c) in E1], 'color': G.GREY, 'size': 5, 'name': 'base E₁'}]
    for t, (u, v) in enumerate(E2):
        items.append({'type': 'curve', 'points': G.arc3((gap[u[1]], u[0] * sy), (gap[v[1]], v[0] * sy), 2.4),
                      'color': G.CORNER[corner(t)], 'width': 2, 'name': ''})
    return out(text, [{'kind': 'svg', 'svg': grid, 'title': 'Figure 4, live', 'figure': 'paperfig-4'},
                      {'kind': '3d', 'title': 'Figure 4 in 3D: the 20 pairs as arches', 'axes': ['column', 'row', ''],
                       'items': items, 'max_width': 1000}], fig='paperfig-4')


# ------------------------------------------------------------------ Figure 5: slopes, and the landscape of M
def run_slopes(params):
    p = json.loads(params)
    n = ival(p, 'n', 9, 3, 24)
    top = ival(p, 'nmax', 12, 6, 30)
    ns = list(range(3, top + 1))
    cert = [(k, RHO_CERT[k][0] / RHO_CERT[k][1]) for k in sorted(RHO_CERT) if k <= top]
    series = [
        {'name': 'n/3 (density 1/3, Lebedev, both sides growing)', 'pts': [(k, k / 3) for k in ns], 'color': '#999', 'dash': True},
        {'name': '(n−1)/2: relaxed numbers z_RL, z_SL, z_2 (Lebedev)', 'pts': [(k, (k - 1) / 2) for k in ns], 'color': '#6A1B9A', 'dash': True},
        {'name': '(n−2)/2: upper bound from Lemma 5.2', 'pts': [(k, (k - 2) / 2) for k in ns], 'color': '#C62828', 'dash': True},
        {'name': 'λ_n: three-block modules (Theorem B)', 'pts': [(k, float(Z.lam(k))) for k in ns], 'color': '#0072B2'},
        {'name': 'κ_n: the canonical base (Theorem D)', 'pts': [(k, float(Z.kappa(k))) for k in ns], 'color': '#E69F00'},
        {'name': 'ρ_n certified (n ≤ 6)', 'pts': cert, 'color': '#009E73', 'mode': 'dots'},
    ]
    if top >= 7:
        series.append({'name': 'n = 7: numerical candidate 1.8 (not certified)', 'pts': [(7, 1.8)], 'color': '#B5530F', 'mode': 'dots'})
    plot = G.lines_svg(series, 'slopes in fixed width: pairs bought by each new row', 'number of columns n',
                       'slope', marker=(n, float(Z.lam(n)), 'λ_%d = %s' % (n, fr(Z.lam(n)))) if n <= top else None)
    pts = G.lattice_points(n)
    best = Z.lam(n)
    Ms = [Z.M_value(*s)[0] for (s, X, Y) in pts]
    F = 1.6 * float(max(Ms) - min(Ms)) or 1.0      # the triangle as wide as the heights vary: a dome, not a needle
    rows3 = [(s, X * F, Y * F, M) for (s, X, Y), M in zip(pts, Ms)]
    items = [{'type': 'points', 'points': [[X, Y, float(M)] for s, X, Y, M in rows3 if M != best], 'color': '#0072B2',
              'size': 4, 'name': 'M(x,y,z), one point per split'},
             {'type': 'points', 'points': [[X, Y, float(M)] for s, X, Y, M in rows3 if M == best], 'color': '#C62828',
              'size': 12, 'marker': 'star', 'name': 'the maximum λ_n: balanced splits'}]
    for fixed in range(1, n - 1):  # lines of constant z, and of constant x, draw the landscape as a net
        line = sorted([(X, Y, float(M)) for s, X, Y, M in rows3 if s[2] == fixed])
        if len(line) > 1:
            items.append({'type': 'curve', 'points': [list(q) for q in line], 'color': '#8fb3cc', 'width': 1, 'name': ''})
        line = sorted([(Y, X, float(M)) for s, X, Y, M in rows3 if s[0] == fixed])
        if len(line) > 1:
            items.append({'type': 'curve', 'points': [[q[1], q[0], q[2]] for q in line], 'color': '#8fb3cc', 'width': 1, 'name': ''})
    for s, lab in (((n - 2, 1, 1), 'A'), ((1, n - 2, 1), 'B'), ((1, 1, n - 2), 'C')):
        X, Y = F * (s[1] + s[2] / 2.0) / n, F * (s[2] * 3 ** 0.5 / 2) / n
        items.append({'type': 'points', 'points': [[X, Y, float(Z.M_value(*s)[0])]], 'color': G.BLOCK[lab], 'size': 8,
                      'name': 'almost everything in block %s' % lab})
    worst = min(rows3, key=lambda r: r[3])
    text = ('n = %d: λ_n = %s ≈ %.4f, κ_n = %s, upper bound (n−2)/2 = %s; certified ρ_n for n ≤ 6: %s. The 3D view '
            'is Proposition 6.3 as a landscape: over every split (x, y, z) of the %d columns into three blocks, the '
            'height is the best ratio M(x,y,z) of pairs to rows. The peak, λ_n, sits exactly at the balanced splits '
            '%s (and their permutations); the most unbalanced split %s gives only %s.' % (
                n, fr(best), float(best), fr(Z.kappa(n)), fr(Fraction(n - 2, 2)),
                ', '.join('ρ_%d = %d/%d' % (k, a, b) for k, (a, b) in sorted(RHO_CERT.items())), n,
                Z.balanced(n), worst[0], fr(worst[3])))
    return out(text, [{'kind': 'svg', 'svg': plot, 'title': 'Figure 5, live', 'figure': 'paperfig-5'},
                      {'kind': '3d', 'title': 'the landscape of the three-block family for n = %d: peak at the balanced split' % n,
                       'axes': ['split (barycentric)', '', 'M(x,y,z)'], 'items': items, 'max_width': 900}], fig='paperfig-5')


# ------------------------------------------------------------------ Figure 6: four columns for your m
def run_f4(params):
    p = json.loads(params)
    m = ival(p, 'm', 30, 6, 400)
    f = Z.f4_formula(m)
    T, E = Z.f4_family(F4_FAMILIES, m)
    E1 = {(i, j) for i, s in enumerate(T) for j in s}
    probs = Z.check(E1, E, m, 4)
    a, b = (2 * m - 3) // 3, (3 * m - 12) // 4
    branch = 'm = 6, the special case' if m == 6 else (
        'first branch ⌊(2m−3)/3⌋ (slope 2/3)' if a > b else ('second branch ⌊(3m−12)/4⌋ (slope 3/4 = ρ₄)' if b > a else
                                                           'both branches equal'))
    exact = F4_EXACT.get(m)
    text = ('m = %d: F₄(m) = %d (%s), so z_L(m,4) = m + 6 + F₄(m) = %d. %s The explicit witness, built here from the '
            'data of the two periodic families: %d rows, |E₁| = %d = m + 6, C₄-free: %s, %d pairs, %s. Profile of its '
            'four triples: %s.' % (
                m, f, branch, m + 6 + f,
                ('The exact computation of the paper (row types, m ≤ 40) gives %d.' % exact) if exact is not None else
                'Beyond m = 40 the value rests on the certificates of Theorem E.',
                len(T), len(E1), Z.c4_free(E1), len(E), ok(probs), Z.profile4(T, E)))
    # the paper's window (6..40) while m is in it; beyond, a window of 40 rows around m, so the steps stay visible
    lo = 6 if m <= 40 else m - 32
    top = 40 if m <= 40 else min(m + 8, 408)
    ms = list(range(lo, top + 1))
    st = G.lines_svg([
        {'name': 'F₄(m), exact', 'pts': [(k, Z.f4_formula(k)) for k in ms], 'color': G.GREY, 'mode': 'step', 'width': 2.2},
        {'name': '⌊(2m−3)/3⌋', 'pts': [(k, (2 * k - 3) // 3) for k in ms], 'color': '#D55E00', 'dash': True, 'width': 1.2},
        {'name': '⌊(3m−12)/4⌋', 'pts': [(k, (3 * k - 12) // 4) for k in ms], 'color': '#0072B2', 'dash': True, 'width': 1.2},
    ], ('F₄(m): two lines that cross at m = 24' if m <= 40 else 'F₄(m) around m = %d (rows %d to %d)' % (m, lo, top)),
       'm', 'pairs', marker=(m, f, 'm = %d: %d' % (m, f)), from_zero=m <= 40)
    tab = G.table_svg(TABLE, highlight=(m, 4) if m <= 14 else None)
    # 3D 1: the table as bars; 3D 2: your witness, pairs as arches over its four columns
    bars = []
    seen = set()
    for e in TABLE:
        col, lab = G.ORIGIN[e['origin']]
        bars += G.bar3(e['n'], e['m'], e['zL'] / 4.0, 0.7, col, name=lab if lab not in seen else '')
        seen.add(lab)
    show = min(m, 80)
    sy = G.row_scale(show, 4)
    items = [{'type': 'points', 'points': [[c, r * sy, 0] for (r, c) in E1 if r < show], 'color': G.GREY, 'size': 4,
              'name': 'base E₁'}]
    named = set()
    for t, (u, v) in enumerate(E):
        if u[0] < show and v[0] < show:
            kind = 'diagonal pair' if u[1] != v[1] else 'vertical pair'
            h = (1.0 if kind == 'diagonal pair' else 0.45) + 0.5 * abs(u[0] - v[0]) * sy
            items.append({'type': 'curve', 'points': G.arc3((u[1], u[0] * sy), (v[1], v[0] * sy), h),
                          'color': '#B5530F' if kind == 'diagonal pair' else '#0072B2', 'width': 1.6,
                          'name': kind if kind not in named else ''})
            named.add(kind)
    return out(text, [{'kind': 'svg', 'svg': tab, 'title': 'Figure 6 (left), live', 'figure': 'paperfig-6'},
                      {'kind': 'svg', 'svg': st, 'title': 'Figure 6 (right), live'},
                      {'kind': '3d', 'title': 'z_L(m, n) as a landscape (height z_L/4), coloured by origin',
                       'axes': ['n', 'm', 'z_L / 4'], 'items': bars, 'max_width': 900},
                      {'kind': '3d', 'title': 'the witness for m = %d%s: its pairs as arches' % (m, '' if m <= 80 else ' (first 80 rows)'),
                       'axes': ['column', 'row', ''], 'items': items, 'max_width': 900}], fig='paperfig-6')


# ------------------------------------------------------------------ Figure 7: the 3 x 3 x 5 box, in cubes
def run_tensor(params):
    p = json.loads(params)
    sep = ival(p, 'spread', 0, 0, 4) * 0.6
    E1 = {tuple(c) for c in TENSOR['E1']}
    default = '; '.join('%d%d%d-%d%d%d' % (tuple(a) + tuple(b)) for a, b in TENSOR['E2'])
    raw = str(p.get('pairs', default)).strip() or default
    try:
        E2 = []
        for part in raw.split(';'):
            ds = [int(ch) for ch in part if ch.isdigit()]
            if len(ds) != 6:
                raise ValueError(part)
            E2.append((tuple(ds[:3]), tuple(ds[3:])))
    except ValueError as e:
        return out('Could not read «%s»: write each pair as two cells ijk-ijk (i, j in 1..3, k in 1..5), pairs separated '
                   'by «;».' % e, [])
    bad_cells = [c for pr in E2 for c in pr if not (1 <= c[0] <= 3 and 1 <= c[1] <= 3 and 1 <= c[2] <= 5)]
    if bad_cells:
        return out('Cells outside 3 × 3 × 5: %s.' % bad_cells, [])
    free = 45 - len(E1)
    probs = Z.box_check(E1, E2)
    bf, _ = Z.box_free(E1)
    rect = [len(Z.full_rectangles({(i - 1, j - 1) for (i, j, k) in E1 if k == kk})) for kk in range(1, 6)]
    text = ('Base: %d cells, box-free: %s; full rectangles per slice %s (sum %d ≤ 9, which is why 34 is the maximum). '
            'Free cells: %d. Your %d pair(s): %s. 4|E₂| = %d %s %d free cells%s.' % (
                len(E1), bf, rect, sum(rect), free, len(E2),
                'admissible ✓ (each at distance ≥ 3 in the box graph, checked here)' if not probs else
                'NOT admissible: ' + '; '.join('pair %s: %s' % ('?' if t is None else t + 1, w) for t, w in probs),
                4 * len(E2), '>' if 4 * len(E2) > free else '≤', free,
                ': the hollow-tetrahedron guess of one quarter fails' if 4 * len(E2) > free and not probs else ''))
    cols = ['#D55E00', '#0072B2', '#CC79A7', '#009E73', '#E69F00', '#6A1B9A']
    pc = {}
    for t, (a, b) in enumerate(E2):
        pc[a] = pc[b] = (cols[t % len(cols)], t)
    # the five slices side by side along the wide axis (k horizontal), each slice a 3 x 3 wall: the box fits the canvas
    # (29-oct: stacked vertically it was taller than the canvas and was cut at the top and bottom)
    def corner(c):
        i, j, k = c
        return (k - 1) * (1 + sep), j - 1, 3 - i     # x = slice, y = column j, z = row i (row 1 on top)

    def centre(c):
        x, y, z = corner(c)
        return [x + 0.43, y + 0.43, z + 0.43]
    items = []
    for c in sorted(E1):
        items += G.cube_faces(*corner(c), 0.86, '#bdbdbd', 0.18, name='base cell' if not items else '')
    named = set()
    for c, (col, t) in pc.items():
        items += G.cube_faces(*corner(c), 0.86, col, 0.85, name='pair %d' % (t + 1) if t not in named else '')
        named.add(t)
    for t, (a, b) in enumerate(E2):
        items.append({'type': 'curve', 'points': [centre(a), centre(b)], 'color': cols[t % len(cols)], 'width': 3,
                      'name': ''})
    empty = [c for c in ((i, j, k) for i in range(1, 4) for j in range(1, 4) for k in range(1, 6))
             if c not in E1 and c not in pc]
    items.append({'type': 'points', 'points': [centre(c) for c in empty], 'color': '#222', 'size': 6,
                  'name': 'empty cell'})
    # the slices, flat (Figure 7, right)
    cs, o = 22, []
    for kk in range(1, 6):
        x0 = 10 + (kk - 1) * (3 * cs + 18)
        o.append('<text x="%d" y="14" font-size="12" text-anchor="middle">k = %d</text>' % (x0 + 1.5 * cs, kk))
        for i in range(1, 4):
            for j in range(1, 4):
                c = (i, j, kk)
                fill = '#bdbdbd' if c in E1 else (pc[c][0] if c in pc else '#fff')
                o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s" stroke="#777"/>'
                         % (x0 + (j - 1) * cs, 22 + (i - 1) * cs, cs, cs, fill))
                if c in pc:
                    o.append('<text x="%d" y="%d" font-size="12" fill="#fff" text-anchor="middle">%d</text>'
                             % (x0 + (j - 1) * cs + cs / 2, 22 + (i - 1) * cs + 16, pc[c][1] + 1))
                elif c not in E1:
                    o.append('<text x="%d" y="%d" font-size="13" text-anchor="middle">×</text>'
                             % (x0 + (j - 1) * cs + cs / 2, 22 + (i - 1) * cs + 16))
    sl = G.svg(5 * (3 * cs + 18) + 10, 3 * cs + 34, o)
    return out(text, [{'kind': 'svg', 'svg': sl, 'title': 'the five slices: grey base, numbered pairs, × empty',
                       'figure': 'paperfig-7'},
                      {'kind': '3d', 'title': 'the 3 × 3 × 5 box: 34 base cells (glass), your pairs in colour, × empty',
                       'axes': ['slice k', 'column j', 'row i'], 'items': items, 'max_width': 900}], fig='paperfig-7')


# ------------------------------------------------------------------ 🎲 random inputs (one per lab; valid by construction)
def random_definition():
    """A random maximum base in the regime m >= C(n,2) and one to three random pairs of free cells (admissible or not:
    the lab says which, and why)."""
    n = random.randint(3, 5)
    m = comb(n, 2) + random.randint(1, 3)
    special = ['%d%d' % (a + 1, b + 1) for a in range(n) for b in range(a + 1, n)]
    single = [str(random.randint(1, n)) for _ in range(m - len(special))]
    rows = special + single
    E1 = {(i, j) for i, r in enumerate(rows) for j in (int(ch) - 1 for ch in r)}
    free = [(i, j) for i in range(m) for j in range(n) if (i, j) not in E1]
    random.shuffle(free)
    if random.random() < 0.5:   # half the throws: a random family grown pair by pair while it stays admissible
        fam = greedy(free, lambda f: not Z.check(E1, f, m, n))
    else:                       # the other half: any pairs at all (the lab shows what goes wrong)
        k = min(len(free) // 2, random.randint(1, 3))
        fam = list(zip(free[0:2 * k:2], free[1:2 * k:2]))
    pairs = '; '.join('%d,%d-%d,%d' % (a[0] + 1, a[1] + 1, b[0] + 1, b[1] + 1) for a, b in fam)
    return json.dumps({'n': str(n), 'base': ' '.join(rows), 'pairs': pairs})


def greedy(cells, admissible, tries=200):
    """A random family: random pairs of the given cells, each kept if the family stays admissible."""
    fam, used = [], set()
    for _ in range(tries):
        a, b = random.sample(cells, 2)
        if a in used or b in used:
            continue
        if admissible(fam + [(a, b)]):
            fam.append((a, b))
            used |= {a, b}
    return fam


def random_blocks():
    n = random.randint(3, 12)
    cuts = sorted(random.sample(range(1, n), 2))
    x, y, z = sorted((cuts[0], cuts[1] - cuts[0], n - cuts[1]), reverse=True)
    # 30-oct (lemmario labcheck: «source» never changed): one throw in five shows the paper's 22 x 5 configuration
    return json.dumps({'n': str(n), 'x': str(x), 'y': str(y), 'z': str(z), 'copies': str(random.randint(1, 3)),
                       'source': 'paper' if random.random() < 0.2 else 'module'})


def random_slopes():
    return json.dumps({'n': str(random.randint(3, 24)), 'nmax': str(random.choice([12, 18, 24, 30]))})


def random_f4():
    return json.dumps({'m': str(random.choice([random.randint(6, 40), random.randint(41, 400)]))})


def random_tensor():
    """One to four random pairs among the 11 free cells of the base (the lab checks each in the box graph)."""
    E1 = {tuple(c) for c in TENSOR['E1']}
    free = [(i, j, k) for i in range(1, 4) for j in range(1, 4) for k in range(1, 6) if (i, j, k) not in E1]
    random.shuffle(free)
    if random.random() < 0.5:   # a random admissible family (how close does chance get to the paper's 3?)
        fam = greedy(free, lambda f: not Z.box_check(E1, f))
    else:
        k = random.randint(1, 4)
        fam = list(zip(free[0:2 * k:2], free[1:2 * k:2]))
    pairs = '; '.join('%d%d%d-%d%d%d' % (a + b) for a, b in fam)
    return json.dumps({'pairs': pairs, 'spread': str(random.choice([0, 0, 1, 2]))})


if __name__ == '__main__':  # local controls (values of the paper) and controls that must fail
    r = json.loads(run_definition(json.dumps({'n': '3', 'base': '12 13 23 1', 'pairs': '4,2-4,3'})))
    assert 'admissible ✓' in r['text'] and '|E₁| + |E₂| = 8' in r['text'], r['text']
    r = json.loads(run_definition(json.dumps({'n': '3', 'base': '12 13 23 1 1', 'pairs': '4,2-4,3; 5,2-5,3'})))
    assert 'NOT admissible' in r['text'], r['text']           # two full rows: a (C3) witness (control)
    r = json.loads(run_blocks(json.dumps({'n': '5', 'copies': '2'})))
    assert 'admissible ✓' in r['text'] and 'P/R = 9/8' in r['text'], r['text'][:300]
    r = json.loads(run_blocks(json.dumps({'n': '7', 'x': '5', 'y': '1', 'z': '1'})))
    assert 'not balanced' in r['text'] and 'admissible ✓' in r['text'], r['text'][:300]
    r = json.loads(run_blocks(json.dumps({'source': 'paper'})))
    assert '|E₂| = 20' in r['text'] and 'admissible ✓' in r['text'], r['text']
    r = json.loads(run_slopes(json.dumps({'n': '9'})))
    assert 'λ_n = 5/2' in r['text'] and '(3, 3, 3)' in r['text'], r['text'][:300]
    for mm, v in ((6, 2), (24, 15), (30, 19), (40, 27)):
        r = json.loads(run_f4(json.dumps({'m': str(mm)})))
        assert 'F₄(m) = %d' % v in r['text'] and 'admissible ✓' in r['text'], r['text'][:300]
    r = json.loads(run_tensor(json.dumps({})))
    assert 'admissible ✓' in r['text'] and '4|E₂| = 12 > 11' in r['text'], r['text']
    r = json.loads(run_tensor(json.dumps({'pairs': '113-215; 121-314; 122-232; 133-234'})))
    assert 'NOT admissible' in r['text'], r['text']             # control: a fourth pair breaks it
    # the dice: 300 random draws per lab must always run (no error, a verdict in the text)
    for rnd, run in ((random_definition, run_definition), (random_blocks, run_blocks), (random_slopes, run_slopes),
                     (random_f4, run_f4), (random_tensor, run_tensor)):
        for _ in range(300 if rnd not in (random_f4, random_blocks) else 40):
            r = json.loads(run(rnd()))
            assert r.get('plots') and 'error' not in r, (rnd.__name__, r.get('text', '')[:200])
            if rnd in (random_blocks, random_f4):
                assert 'admissible ✓' in r['text'], r['text'][:200]   # the constructions are always admissible
    print('controls: OK (dice included)')
