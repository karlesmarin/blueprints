# encaje: DIBUJO de los laboratorios del blueprint zl-three-blocks (Python puro, Pyodide): cuadrícula SVG transpuesta como la Fig. 4, arcos 3D de los pares, cubos 3D, escalera de F_4, tabla coloreada, paisaje de M sobre el símplex
"""Only drawing: every number comes from zl_core."""
import math

BLOCK = {'A': '#E69F00', 'B': '#56B4E9', 'C': '#009E73'}       # the paper's block colours (Okabe-Ito)
CORNER = {'A': '#D55E00', 'B': '#0072B2', 'C': '#CC79A7'}      # angle of the hollow triangle at A, B, C
GREY, INK, RED = '#4D4D4D', '#222222', '#C62828'


def esc(s):
    return str(s).replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def svg(w, h, body):
    return ('<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg" '
            'font-family="serif">%s</svg>' % (w, h, ''.join(body)))


# ------------------------------------------------------------------ grids
def grid_svg(m, n, E1, E2, colour_of_pair=None, col_colour=None, bad=(), marks=(), title='', transpose=True,
             row_labels=None, max_rows=60):
    """The m x n grid (rows horizontal when transpose, as Figure 4): base cells grey, each pair numbered in its two
    cells, columns tinted by block; ``bad``: pair indices to ring in red; ``marks``: cells to ring (witnesses)."""
    mm = min(m, max_rows)
    cs = max(9, min(22, int(760 / max(mm, 1)))) if transpose else max(14, min(30, int(420 / max(n, 1))))
    W = (mm if transpose else n) * cs + 70
    H = (n if transpose else mm) * cs + 60
    o = ['<text x="%d" y="16" font-size="13" text-anchor="middle">%s</text>' % (W / 2, esc(title))]

    def xy(r, c):
        return (50 + r * cs, 30 + c * cs) if transpose else (50 + c * cs, 30 + r * cs)
    for r in range(mm):
        for c in range(n):
            x, y = xy(r, c)
            tint = col_colour(c) if col_colour else None
            o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s" fill-opacity="%s" stroke="#ccc" '
                     'stroke-width="0.5"/>' % (x, y, cs, cs, tint or '#fff', '0.12' if tint else '1'))
    for (r, c) in E1:
        if r < mm:
            x, y = xy(r, c)
            o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s"/>'
                     % (x + cs * .12, y + cs * .12, cs * .76, cs * .76, GREY))
    for t, (a, b) in enumerate(E2):
        col = colour_of_pair(t) if colour_of_pair else '#B5530F'
        for (r, c) in (a, b):
            if r < mm:
                x, y = xy(r, c)
                o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" fill-opacity="0.85" '
                         'stroke="%s" stroke-width="%s"/>' % (x + cs * .1, y + cs * .1, cs * .8, cs * .8, col,
                                                              RED if t in bad else 'none', 2.5 if t in bad else 0))
                if cs >= 12:
                    o.append('<text x="%.1f" y="%.1f" font-size="%d" text-anchor="middle" fill="#fff">%d</text>'
                             % (x + cs / 2, y + cs * .68, max(7, cs * .45), t + 1))
    for (r, c) in marks:
        if r < mm:
            x, y = xy(r, c)
            o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="none" stroke="%s" stroke-width="2.5" '
                     'stroke-dasharray="3 2"/>' % (x + 1, y + 1, cs - 2, cs - 2, RED))
    for r in range(mm):
        x, y = xy(r, n if transpose else 0)
        lab = row_labels[r] if row_labels else (str(r + 1) if (mm <= 30 or r % 5 == 4) else '')
        if transpose:
            o.append('<text x="%.1f" y="%.1f" font-size="9" text-anchor="middle">%s</text>' % (x + cs / 2, y + 12, esc(lab)))
        else:
            o.append('<text x="44" y="%.1f" font-size="9" text-anchor="end">%s</text>' % (30 + r * cs + cs * .7, esc(lab)))
    for c in range(n):
        x, y = xy(0, c)
        if transpose:
            o.append('<text x="44" y="%.1f" font-size="9" text-anchor="end">%d</text>' % (y + cs * .7, c + 1))
        else:
            o.append('<text x="%.1f" y="26" font-size="9" text-anchor="middle">%d</text>' % (x + cs / 2, c + 1))
    if m > mm:
        o.append('<text x="%d" y="%d" font-size="10" fill="#777">… %d more rows (all checked)</text>' % (50, H - 6, m - mm))
    return svg(W, H, o)


def template_svg(sizes, groups, M):
    """Figure 3 (right) for your sizes: columns by block (widths to scale), rows grouped by type (heights to scale);
    groups: [(type, count)]."""
    W, H, L, T = 560, 330, 150, 40
    total_c, total_r = sum(sizes), sum(c for _, c in groups) or 1
    xs, x = {}, L
    for b, s in zip('ABC', sizes):
        xs[b] = (x, x + (W - L - 20) * s / total_c)
        x = xs[b][1]
    o = ['<text x="%d" y="16" font-size="13" text-anchor="middle">the template for blocks of sizes %s (to scale): '
         'M = %s</text>' % (W / 2, '(%d, %d, %d)' % tuple(sizes), esc(M))]
    for b in 'ABC':
        o.append('<text x="%.1f" y="34" font-size="12" text-anchor="middle" fill="%s" font-weight="bold">%s</text>'
                 % ((xs[b][0] + xs[b][1]) / 2, BLOCK[b], b))
    y = T
    for typ, cnt in groups:
        h = (H - T - 10) * cnt / total_r
        for b in 'ABC':
            on = b in typ
            o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" fill-opacity="%s" stroke="#777" '
                     'stroke-width="0.6"/>' % (xs[b][0], y, xs[b][1] - xs[b][0], h, BLOCK[b] if on else '#fff',
                                               0.55 if on else 1))
            if not on and h > 12:
                o.append('<text x="%.1f" y="%.1f" font-size="10" fill="#777" font-style="italic" text-anchor="middle">'
                         'empty</text>' % ((xs[b][0] + xs[b][1]) / 2, y + h / 2 + 3))
        o.append('<text x="%d" y="%.1f" font-size="11" text-anchor="end">%d rows of type %s</text>'
                 % (L - 6, y + h / 2 + 4, cnt, typ))
        y += h
    return svg(W, H, o)


# ------------------------------------------------------------------ 3D pieces
def row_scale(rows, width, ratio=1.6):
    """Factor for the row axis so that a grid of ``rows`` rows and ``width`` columns looks ratio : 1 in 3D (the
    viewer keeps one scale for the three axes)."""
    return max(0.05, min(1.0, ratio * width / max(rows, 1)))


def arc3(a, b, h, steps=14):
    """A parabolic arch over the plane z = 0 from a = (x, y) to b."""
    return [[a[0] + (b[0] - a[0]) * t / steps, a[1] + (b[1] - a[1]) * t / steps,
             h * 4 * (t / steps) * (1 - t / steps)] for t in range(steps + 1)]


def cube_faces(x, y, z, s, color, opacity, name=''):
    """A cube [x, x+s] x [y, y+s] x [z, z+s] as six flat surfaces."""
    return box_faces((x, x + s), (y, y + s), (z, z + s), color, opacity, name)


def box_faces(X, Y, Z, color, opacity, name=''):
    """The box X x Y x Z (each a pair of ends) as six flat surfaces."""
    faces = [
        [[[X[0], Y[0], Z[0]], [X[0], Y[1], Z[0]]], [[X[1], Y[0], Z[0]], [X[1], Y[1], Z[0]]]],
        [[[X[0], Y[0], Z[1]], [X[0], Y[1], Z[1]]], [[X[1], Y[0], Z[1]], [X[1], Y[1], Z[1]]]],
        [[[X[0], Y[0], Z[0]], [X[0], Y[0], Z[1]]], [[X[1], Y[0], Z[0]], [X[1], Y[0], Z[1]]]],
        [[[X[0], Y[1], Z[0]], [X[0], Y[1], Z[1]]], [[X[1], Y[1], Z[0]], [X[1], Y[1], Z[1]]]],
        [[[X[0], Y[0], Z[0]], [X[0], Y[0], Z[1]]], [[X[0], Y[1], Z[0]], [X[0], Y[1], Z[1]]]],
        [[[X[1], Y[0], Z[0]], [X[1], Y[0], Z[1]]], [[X[1], Y[1], Z[0]], [X[1], Y[1], Z[1]]]],
    ]
    return [{'type': 'surface', 'grid': g, 'color': color, 'opacity': opacity, 'name': name if k == 0 else ''}
            for k, g in enumerate(faces)]


def bar3(x, y, h, w, color, name=''):
    """A vertical bar of height h on the square of side w centred at (x, y)."""
    return box_faces((x - w / 2, x + w / 2), (y - w / 2, y + w / 2), (0, h), color, 0.75, name)


# ------------------------------------------------------------------ 2D plots
def lines_svg(series, title, xlabel, ylabel, marker=None, W=580, H=330):
    """series: [{'name', 'pts': [(x, y)], 'color', 'mode': 'line'|'dots'|'step', 'dash'}]."""
    xs = [p[0] for s in series for p in s['pts']]
    ys = [p[1] for s in series for p in s['pts']]
    x0, x1, y0, y1 = min(xs), max(xs), min(0, min(ys)), max(ys) * 1.05
    L, R, T, B = 52, 14, 30, 42
    X = lambda v: L + (v - x0) / ((x1 - x0) or 1) * (W - L - R)
    Y = lambda v: H - B - (v - y0) / ((y1 - y0) or 1) * (H - T - B)
    o = ['<text x="%d" y="16" font-size="13" text-anchor="middle">%s</text>' % (W / 2, esc(title))]
    for i in range(6):
        v = y0 + (y1 - y0) * i / 5
        o.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#eee"/><text x="%d" y="%.1f" font-size="10" '
                 'text-anchor="end">%.3g</text>' % (L, W - R, Y(v), Y(v), L - 4, Y(v) + 3, v))
    step = max(1, int(round((x1 - x0) / 8.0)))   # the x axis counts columns or rows: integer ticks
    xv = int(math.ceil(x0))
    while xv <= x1:
        o.append('<text x="%.1f" y="%d" font-size="10" text-anchor="middle">%d</text>' % (X(xv), H - B + 14, xv))
        xv += step
    for k, s in enumerate(series):
        c = s.get('color', INK)
        pts = s['pts']
        if s.get('mode') == 'dots':
            for (x, y) in pts:
                o.append('<circle cx="%.1f" cy="%.1f" r="4" fill="%s"/>' % (X(x), Y(y), c))
        elif len(pts) > 1:
            if s.get('mode') == 'step':
                d = 'M%.1f %.1f' % (X(pts[0][0]), Y(pts[0][1]))
                for (xa, ya), (xb, yb) in zip(pts, pts[1:]):
                    d += ' L%.1f %.1f L%.1f %.1f' % (X(xb), Y(ya), X(xb), Y(yb))
            else:
                d = 'M' + ' L'.join('%.1f %.1f' % (X(x), Y(y)) for x, y in pts)
            o.append('<path d="%s" fill="none" stroke="%s" stroke-width="%s"%s/>'
                     % (d, c, s.get('width', 1.8), ' stroke-dasharray="5 4"' if s.get('dash') else ''))
        o.append('<rect x="%d" y="%d" width="12" height="3" fill="%s"/><text x="%d" y="%d" font-size="11">%s</text>'
                 % (L + 8, T + 2 + 14 * k, c, L + 24, T + 7 + 14 * k, esc(s['name'])))
    if marker:
        mx, my, lab = marker
        o.append('<circle cx="%.1f" cy="%.1f" r="6" fill="none" stroke="%s" stroke-width="2.5"/><text x="%.1f" '
                 'y="%.1f" font-size="11" fill="%s">%s</text>' % (X(mx), Y(my), RED, X(mx) + 8, Y(my) - 8, RED, esc(lab)))
    o.append('<text x="%d" y="%d" text-anchor="middle" font-size="12">%s</text>' % (W / 2, H - 8, esc(xlabel)))
    o.append('<text x="13" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 13 %d)">%s</text>'
             % (H / 2, H / 2, esc(ylabel)))
    return svg(W, H, o)


ORIGIN = {'publicado': ('#D9D9D9', 'previously published'), 'nuevo': ('#009E73', 'new exact value'),
          'cota': ('#E69F00', 'lower and upper bounds')}


def table_svg(entries, highlight=None):
    """Figure 6 (left): z_L(m, n), coloured by origin."""
    ms = sorted({e['m'] for e in entries})
    ns = sorted({e['n'] for e in entries})
    cw, ch = 46, 22
    W, H = 60 + cw * len(ns), 50 + ch * len(ms) + 54
    o = ['<text x="%d" y="16" font-size="13" text-anchor="middle">z_L(m, n): exact values and bounds</text>' % (W / 2)]
    for j, n in enumerate(ns):
        o.append('<text x="%d" y="40" font-size="11" text-anchor="middle">n = %d</text>' % (60 + cw * j + cw / 2, n))
    for i, m in enumerate(ms):
        o.append('<text x="52" y="%d" font-size="11" text-anchor="end">m = %d</text>' % (50 + ch * i + 15, m))
    for e in entries:
        i, j = ms.index(e['m']), ns.index(e['n'])
        col = ORIGIN[e['origin']][0]
        txt = str(e['zL']) if e['origin'] != 'cota' else '%d–%d' % (e['zL'], e['upper'])
        hi = highlight and (e['m'], e['n']) == highlight
        o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s" stroke="%s" stroke-width="%s"/>'
                 % (60 + cw * j, 50 + ch * i, cw - 2, ch - 2, col, RED if hi else '#fff', 2.5 if hi else 1))
        o.append('<text x="%d" y="%d" font-size="11" text-anchor="middle" fill="%s">%s</text>'
                 % (60 + cw * j + cw / 2 - 1, 50 + ch * i + 15, '#fff' if e['origin'] == 'nuevo' else INK, txt))
    for k, (key, (col, lab)) in enumerate(ORIGIN.items()):
        y = 50 + ch * len(ms) + 16 + 14 * k
        o.append('<rect x="60" y="%d" width="12" height="10" fill="%s"/><text x="78" y="%d" font-size="11">%s</text>'
                 % (y - 9, col, y, lab))
    return svg(W, H, o)


def lattice_points(n):
    """Every ordered split (x, y, z) of n into three positive parts, on the triangle (barycentric layout)."""
    out = []
    for x in range(1, n - 1):
        for y in range(1, n - x):
            z = n - x - y
            out.append(((x, y, z), (y + z / 2.0) / n, (z * math.sqrt(3) / 2) / n))
    return out
