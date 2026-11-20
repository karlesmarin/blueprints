# encaje: dibujo de los laboratorios del blueprint real-rational-integer (Python puro, SVG; corre en el navegador).
"""Each lab draws its own object: the graph and its ladder of levels, the strip of n, the rotation, the loosened bond."""
import math
from html import escape

AZ, NA, VE, GR, TX, SE, RO = '#2a78d6', '#eb6834', '#1baf7a', '#b9b8b2', '#0b0b0b', '#52514e', '#c62828'


def _svg(w, h, body, title):
    s = ('<svg viewBox="0 0 %d %d" width="%d" style="max-width:100%%;height:auto;background:#fff;display:block" '
         'xmlns="http://www.w3.org/2000/svg" font-family="sans-serif">%s</svg>' % (w, h, w, ''.join(body)))
    return {'kind': 'svg', 'svg': s, 'title': ''}


def _t(x, y, s, size=13, col=TX, anchor='middle', weight='normal'):
    return '<text x="%.1f" y="%.1f" font-size="%d" fill="%s" text-anchor="%s" font-weight="%s">%s</text>' % (x, y, size, col, anchor, weight, escape(str(s)))


def _l(x1, y1, x2, y2, col=GR, w=1.5, dash=None):
    d = ' stroke-dasharray="%s"' % dash if dash else ''
    return '<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="%s" stroke-width="%.1f" stroke-linecap="round"%s/>' % (x1, y1, x2, y2, col, w, d)


def _dash(x1, y, x2, col, w=4):
    """A data dash as a rounded rect (21-nov: labweb counts rect/path/circle as data, not bare lines, so a figure drawn
    only with <line> read as empty; axes stay lines)."""
    return '<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" rx="%.1f" fill="%s"/>' % (x1, y - w / 2, x2 - x1, w, w / 2, col)


def _c(x, y, r, fill, stroke='#fff', w=2):
    return '<circle cx="%.1f" cy="%.1f" r="%.1f" fill="%s" stroke="%s" stroke-width="%.1f"/>' % (x, y, r, fill, stroke, w)


def graph(n, edges, title, vcol=None, ecol=None, size=300, leyenda=False):
    """Vertices on a circle, numbered from 1."""
    cx = cy = size / 2
    R = size * .36
    P = [(cx + R * math.sin(2 * math.pi * i / n), cy - R * math.cos(2 * math.pi * i / n)) for i in range(n)] if n > 1 else [(cx, cy)]
    b = [_t(cx, 16, title, 13, SE)]
    for a, c in edges:
        b.append(_l(P[a][0], P[a][1], P[c][0], P[c][1], (ecol or {}).get((a, c), AZ), 3))
    for i, (x, y) in enumerate(P):
        b.append(_c(x, y, 12, (vcol or {}).get(i, AZ)))
        b.append(_t(x, y + 4, i + 1, 11, '#fff', weight='bold'))
    alto = size
    if leyenda:
        alto = size + 22
        for k, (f, x) in enumerate(((AZ, 'ring'), (NA, 'chain'), (GR, 'lone'), (RO, 'degree ≥ 3'))):
            b.append(_c(18 + 66 * k, size + 8, 6, f, f, 0))
            b.append(_t(28 + 66 * k, size + 12, x, 11, SE, 'start'))
    return _svg(size, alto, b, title)


def ladder(lv, title):
    """lv = [[level, multiplicity], ...] with level in [−1, 1]: one dash per copy."""
    w, h = 340, 300
    Y = lambda v: 150 - 118 * v                                          # noqa: E731
    b = [_t(w / 2, 16, title, 13, SE), _l(52, Y(1), 52, Y(-1), GR, 1)]
    for v in (1, 0, -1):
        b += [_l(48, Y(v), 56, Y(v), GR, 1), _t(42, Y(v) + 4, v, 11, SE, 'end')]
    for v, m in lv:
        borde = abs(abs(v) - 1) < 1e-8
        col = GR if borde else (AZ if m % 2 == 0 else NA)
        for k in range(min(m, 6)):
            b.append(_dash(72 + 42 * k, Y(v), 106 + 42 * k, col, 4))
    b += [_l(70, 284, 88, 284, AZ, 4), _t(92, 288, 'paired', 11, SE, 'start'), _l(146, 284, 164, 284, NA, 4), _t(168, 288, 'alone', 11, SE, 'start'),
          _l(214, 284, 232, 284, GR, 4), _t(236, 288, '±1: free', 11, SE, 'start')]
    return _svg(w, h, b, title)


def strip(n, sq, title):
    """Odd numbers 3..129 in a grid; the current n is ringed."""
    cols, cell = 16, 34
    ns = list(range(3, 130, 2))
    rows = (len(ns) + cols - 1) // cols
    w, h = cols * cell + 20, rows * cell + 66
    b = [_t(w / 2, 16, title, 13, SE)]
    for i, v in enumerate(ns):
        x, y = 10 + (i % cols) * cell, 28 + (i // cols) * cell
        a, c = sq(v), sq(v - 2)
        f = AZ if a else (VE if c else '#ececea')
        ring = TX if v == n else 'none'
        b.append('<rect x="%d" y="%d" width="%d" height="%d" rx="4" fill="%s" stroke="%s" stroke-width="2.5"/>' % (x, y, cell - 4, cell - 4, f, ring))
        b.append(_t(x + (cell - 4) / 2, y + 20, v, 11, '#fff' if a or c else SE))
    y = 28 + rows * cell + 14
    for x, f, s in ((14, AZ, 'n is a square'), (150, VE, 'n − 2 is a square'), (310, '#ececea', 'gap: ℓ_Q > n')):
        b.append('<rect x="%d" y="%d" width="14" height="14" rx="3" fill="%s"/>' % (x, y - 11, f))
        b.append(_t(x + 20, y, s, 12, SE, 'start'))
    return _svg(w, h, b, title)


def rotation(lam, delta, title):
    """The plane of a level: cosine λ and sine √δ of the rotation."""
    w, h = 300, 300
    cx, cy, R = 150, 160, 105
    th = math.acos(max(-1, min(1, float(lam))))
    x, y = cx + R * math.cos(th), cy - R * math.sin(th)
    b = [_t(w / 2, 16, title, 13, SE), '<circle cx="%d" cy="%d" r="%d" fill="none" stroke="%s"/>' % (cx, cy, R, GR),
         _l(cx - R - 12, cy, cx + R + 12, cy, GR, 1), _l(cx, cy - R - 12, cx, cy + R + 12, GR, 1),
         _l(cx, cy, x, y, AZ, 3), _l(cx, cy, x, cy, NA, 4), _l(x, cy, x, y, VE, 4), _c(x, y, 6, AZ)]
    b += [_t((cx + x) / 2, cy + 18, 'cos θ = ' + str(lam), 12, NA), _t(x + (10 if x >= cx else -10), (cy + y) / 2, 'sin²θ = ' + str(delta), 12, '#128a5f', 'start' if x >= cx else 'end')]
    return _svg(w, h, b, title)


def primes(rows, title):
    """rows = [(label, state)], state in 'ok', 'free', 'bad'."""
    w = 340
    h = 40 + 30 * max(1, len(rows))
    b = [_t(w / 2, 16, title, 13, SE)]
    color = {'ok': VE, 'free': '#ececea', 'bad': RO}
    for i, (s, e) in enumerate(rows):
        y = 30 + 30 * i
        b.append('<rect x="10" y="%d" width="320" height="24" rx="4" fill="%s"/>' % (y, color[e]))
        b.append(_t(20, y + 16, s, 12, TX if e == 'free' else '#fff', 'start'))
    return _svg(w, h, b, title)


def bond(n, a, title):
    """The ring with its last bond of weight a."""
    size = 300
    cx = cy = 155
    R = 105
    P = [(cx + R * math.sin(2 * math.pi * i / n), cy - R * math.cos(2 * math.pi * i / n)) for i in range(n)]
    b = [_t(150, 16, title, 13, SE)]
    for i in range(n - 1):
        b.append(_l(P[i][0], P[i][1], P[i + 1][0], P[i + 1][1], AZ, 3.5))
    col = '#eda100' if a < 0 else AZ
    if abs(a) < 1e-9:
        b.append(_l(P[-1][0], P[-1][1], P[0][0], P[0][1], GR, 1.2, '4 5'))
    else:
        b.append(_l(P[-1][0], P[-1][1], P[0][0], P[0][1], col, .6 + 3 * abs(a), None if abs(a) > .999 else '7 4'))
    for x, y in P:
        b.append(_c(x, y, 9, AZ))
    return _svg(size, size, b, title)


def semicircle(a, title):
    w, h = 340, 220
    X = lambda v: 170 + 130 * v                                          # noqa: E731
    Y = lambda v: 180 - 130 * v                                          # noqa: E731
    pts = ' '.join('%.1f,%.1f' % (X(-1 + i / 50), Y(math.sqrt(max(0, 1 - (-1 + i / 50)**2)))) for i in range(101))
    c = math.sqrt(max(0, 1 - a * a))
    b = [_t(w / 2, 16, title, 13, SE), _l(X(-1.1), Y(0), X(1.1), Y(0), GR, 1), '<polyline points="%s" fill="none" stroke="%s" stroke-width="3"/>' % (pts, NA),
         _l(X(a), Y(0), X(a), Y(c), SE, 1, '3 3'), _c(X(-1), Y(0), 6, AZ), _c(X(1), Y(0), 6, AZ), _c(X(a), Y(c), 7, NA),
         _t(X(-1), 200, '−1', 12, SE), _t(X(1), 200, '1', 12, SE), _t(X(0), 200, 'weight a', 12, SE), _t(X(a), max(30, Y(c) - 12), '%.3f' % c, 12, TX)]
    return _svg(w, h, b, title)
