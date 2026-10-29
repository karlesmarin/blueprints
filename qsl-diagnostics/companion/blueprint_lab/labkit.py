# encaje: kit común de los laboratorios de Lemmario (Python puro; corre en el navegador con Pyodide y en local).
"""labkit: small drawing helpers for the labs of every blueprint, so that a lab only computes its figure.

A lab function receives a JSON string of inputs and returns json.dumps({'text', 'table', 'plots', 'error'}). The
helpers build the plots:

- ``svg_plot(series, ...)``: a 2D figure (points or lines) as {'kind': 'svg', ...}; replaces Figure N of the paper
  when given ``figure='paperfig-N'``;
- ``clock(points_on, n, ...)``: n positions on a circle, some marked, optional polygon (cyclic structures);
- ``three_d(items, ...)`` and the item helpers ``points3``, ``curve3``, ``surface3``: a turnable 3D figure, with an
  optional slider (one list of items per value) — think of the 3D that tells THIS figure's idea best (a torus for a
  cyclic group, a surface for a function of two parameters, a cloud with a slider for a family…), never a default one;
- ``table(head, rows)`` and ``result(...)`` to assemble the answer;
- ``error(msg)`` for bad input.
Copy it next to the lab (``files = ['lab/<slug>_lab.py', 'lab/labkit.py']``)."""
import json
import math

PALETTE = ['#1B6F8C', '#B5530F', '#2E7D32', '#6A1B9A', '#C62828', '#455A64']


def esc(s):
    return str(s).replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def svg_plot(series, title='', xlabel='', ylabel='', width=560, height=320, figure=None, logy=False):
    """series: [{'name', 'x': [...], 'y': [...], 'mode': 'points'|'line', 'color', 'size': [...] or number,
    'highlight': [bool, ...]}].

    30-oct (qsl-diagnostics, seen with random inputs): the legend goes BELOW the plot, never over the data; the data
    range has a 6 % margin, so that a point at an extreme is not cut by the frame; lines and points are clipped to the
    frame."""
    xs = [x for s in series for x in s['x']]
    ys = [(math.log10(y) if logy and y > 0 else y) for s in series for y in s['y']]
    if not xs:
        return {'kind': 'svg', 'svg': '<svg xmlns="http://www.w3.org/2000/svg"/>', 'title': title}
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    py = 0.06 * ((y1 - y0) or abs(y1) or 1)
    y0, y1 = y0 - py, y1 + py
    names = [s.get('name', '') for s in series if s.get('name')]
    rows = (len(names) + 1) // 2
    L, R, T, B = 60, 16, 16, 44
    H = height + 16 * rows                       # the plot keeps its height; the legend adds its rows below
    X = lambda v: L + (v - x0) / ((x1 - x0) or 1) * (width - L - R)
    Y = lambda v: height - B - ((math.log10(v) if logy and v > 0 else v) - y0) / ((y1 - y0) or 1) * (height - T - B)
    clip = 'lmclip%d' % (abs(hash((title, len(xs), x0, x1, y0, y1))) % 10 ** 8)
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">'
         % (width, H),
         '<defs><clipPath id="%s"><rect x="%d" y="%d" width="%d" height="%d"/></clipPath></defs>'
         % (clip, L - 6, T - 6, width - L - R + 12, height - T - B + 12)]
    for i in range(6):  # grid and ticks
        v = y0 + (y1 - y0) * i / 5
        y = height - B - (height - T - B) * i / 5
        o.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#eee"/>' % (L, width - R, y, y))
        o.append('<text x="%d" y="%.1f" font-size="10" text-anchor="end">%s</text>'
                 % (L - 4, y + 3, ('1e%.1f' % v) if logy else ('%.3g' % v)))
        xv = x0 + (x1 - x0) * i / 5
        o.append('<text x="%.1f" y="%d" font-size="10" text-anchor="middle">%.3g</text>'
                 % (L + (width - L - R) * i / 5, height - B + 14, xv))
    o.append('<g clip-path="url(#%s)">' % clip)
    leg = []
    for k, s in enumerate(series):
        c = s.get('color', PALETTE[k % len(PALETTE)])
        pts = list(zip(s['x'], s['y']))
        if s.get('mode') == 'line' and len(pts) > 1:
            o.append('<path d="M%s" fill="none" stroke="%s" stroke-width="2"/>'
                     % (' L'.join('%.1f %.1f' % (X(x), Y(y)) for x, y in pts), c))
        else:
            sizes = s.get('size', 3)
            hi = s.get('highlight')
            for i, (x, y) in enumerate(pts):
                r = sizes[i] if isinstance(sizes, list) else sizes
                col = PALETTE[1] if hi and hi[i] else c
                o.append('<circle cx="%.1f" cy="%.1f" r="%.1f" fill="%s" fill-opacity="0.65"/>' % (X(x), Y(y), r, col))
        if s.get('name'):
            leg.append((c, s['name']))
    o.append('</g>')
    o.append('<text x="%d" y="%d" text-anchor="middle" font-size="12">%s</text>' % (width / 2, height - 8, esc(xlabel)))
    o.append('<text x="14" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 14 %d)">%s</text>'
             % (height / 2, height / 2, esc(ylabel)))
    for k, (c, n) in enumerate(leg):
        lx, ly = L + (k % 2) * (width - L - R) / 2, height + 4 + 16 * (k // 2)
        o.append('<rect x="%.1f" y="%d" width="10" height="3" fill="%s"/><text x="%.1f" y="%d" font-size="11">%s</text>'
                 % (lx, ly, c, lx + 14, ly + 4, esc(n)))
    o.append('</svg>')
    out = {'kind': 'svg', 'svg': ''.join(o), 'title': title}
    if figure:
        out['figure'] = figure
    return out


def clock(marked, n=12, labels=None, polygon=None, colour='#1B6F8C', title='', cx=150, size=300):
    """n positions on a circle, the ``marked`` ones filled; ``polygon``: positions joined in that order."""
    R, cy = size * 0.33, size * 0.52
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">'
         % (2 * cx, size), '<text x="%d" y="18" text-anchor="middle" font-size="13">%s</text>' % (cx, esc(title)),
         '<circle cx="%d" cy="%.1f" r="%.1f" fill="none" stroke="#bbb"/>' % (cx, cy, R)]
    pos = {}
    for p in range(n):
        a = math.pi / 2 - 2 * math.pi * p / n
        x, y = cx + R * math.cos(a), cy - R * math.sin(a)
        pos[p] = (x, y)
        on = p in marked
        o.append('<circle cx="%.1f" cy="%.1f" r="%s" fill="%s" stroke="#888"/>' % (x, y, 6 if on else 3.5,
                                                                                  colour if on else '#fff'))
        o.append('<text x="%.1f" y="%.1f" text-anchor="middle" font-size="11">%s</text>'
                 % (cx + (R + 15) * math.cos(a), cy - (R + 15) * math.sin(a) + 4, esc(labels[p] if labels else p)))
    if polygon and len(polygon) > 1:
        o.append('<path d="M%s" fill="none" stroke="%s" stroke-dasharray="4 3"/>'
                 % (' L'.join('%.1f %.1f' % pos[p] for p in polygon), colour))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': ''}


def points3(pts, name='', color=None, size=5, star=False, opacity=0.8):
    return {'type': 'points', 'points': pts, 'name': name, 'color': color or PALETTE[0], 'size': size,
            'marker': 'star' if star else 'dot', 'opacity': opacity}


def curve3(pts, name='', color=None, width=2, dash=False):
    return {'type': 'curve', 'points': pts, 'name': name, 'color': color or PALETTE[2], 'width': width, 'dash': dash}


def surface3(f, xs, ys, name='', color=None, opacity=0.5):
    """The surface z = f(x, y) over the grid xs × ys (or a parametrisation: f returns [x, y, z])."""
    grid = []
    for x in xs:
        row = []
        for y in ys:
            v = f(x, y)
            row.append(list(v) if isinstance(v, (list, tuple)) else [x, y, v])
        grid.append(row)
    return {'type': 'surface', 'grid': grid, 'name': name, 'color': color or '#c9d6e3', 'opacity': opacity}


def three_d(items, title='', axes=('x', 'y', 'z'), slider=None):
    """slider: {'label', 'values': [...], 'items': [[items for value 1], [items for value 2], ...]}."""
    out = {'kind': '3d', 'title': title, 'axes': list(axes), 'items': items}
    if slider:
        out['slider'] = slider
    return out


def table(head, rows):
    return {'head': [str(h) for h in head], 'rows': [[str(x) for x in r] for r in rows]}


def result(text='', plots=(), table=None):
    out = {'text': text, 'plots': list(plots)}
    if table:
        out['table'] = table
    return json.dumps(out)


def error(msg):
    return json.dumps({'error': msg})
