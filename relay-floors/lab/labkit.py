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


def _tick(v):
    """An axis value a reader can read: 6010 rather than 6.01e+03, 0.42 rather than 4.2e-01 (31-oct)."""
    a = abs(v)
    if a >= 100:
        return '%.0f' % v
    if a >= 1 or a == 0:
        return ('%.1f' % v).rstrip('0').rstrip('.')
    return '%.2g' % v


def svg_plot(series, title='', xlabel='', ylabel='', width=560, height=320, figure=None, logy=False, logx=False):
    """series: [{'name', 'x': [...], 'y': [...], 'mode': 'points'|'line', 'color', 'size': [...] or number,
    'highlight': [bool, ...]}].

    30-oct (qsl-diagnostics, seen with random inputs): the legend goes BELOW the plot, never over the data; the data
    range has a 6 % margin, so that a point at an extreme is not cut by the frame; lines and points are clipped to the
    frame."""
    lx = lambda v: math.log10(v) if logx and v > 0 else v
    xs = [lx(x) for s in series for x in s['x']]
    ys = [(math.log10(y) if logy and y > 0 else y) for s in series for y in s['y']]
    if not xs:
        return {'kind': 'svg', 'svg': '<svg xmlns="http://www.w3.org/2000/svg"/>', 'title': title}
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    py = 0.06 * ((y1 - y0) or abs(y1) or 1)
    y0, y1 = y0 - py, y1 + py
    names = [s.get('name', '') for s in series if s.get('name')]
    # 31-oct (Carles: «algunos textos se montan»): two legend columns only when every name fits in half the width
    # (≈ 6 px per character at 11 px); otherwise one entry per line
    cols = 2 if all(len(n) * 6.0 + 18 < (width - 76) / 2 for n in names) else 1
    rows = (len(names) + cols - 1) // cols
    L, R, T, B = 60, 16, 16, 44
    H = height + 16 * rows                       # the plot keeps its height; the legend adds its rows below
    px = 0.03 * ((x1 - x0) or 1)
    x0, x1 = x0 - px, x1 + px
    X = lambda v: L + (lx(v) - x0) / ((x1 - x0) or 1) * (width - L - R)
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
                 % (L - 4, y + 3, _tick(10 ** v) if logy else _tick(v)))
        xv = x0 + (x1 - x0) * i / 5
        xv = 10 ** xv if logx else xv
        o.append('<text x="%.1f" y="%d" font-size="10" text-anchor="middle">%s</text>'
                 % (L + (width - L - R) * i / 5, height - B + 14, _tick(xv)))
    o.append('<g clip-path="url(#%s)">' % clip)
    leg = []
    for k, s in enumerate(series):
        c = s.get('color', PALETTE[k % len(PALETTE)])
        pts = list(zip(s['x'], s['y']))
        if s.get('mode') == 'area' and len(pts) > 1:   # 31-oct (relay-floors): hatched region BELOW the line
            pid = 'hatch%d%d' % (k, abs(hash(clip)) % 10 ** 6)
            o.append('<defs><pattern id="%s" width="6" height="6" patternUnits="userSpaceOnUse" '
                     'patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="6" stroke="%s" stroke-width="1.2" '
                     'stroke-opacity="0.55"/></pattern></defs>' % (pid, c))
            base = height - B + 6
            d = 'M%.1f %.1f L' % (X(pts[0][0]), base) + ' L'.join('%.1f %.1f' % (X(x), Y(y)) for x, y in pts) + \
                ' L%.1f %.1f Z' % (X(pts[-1][0]), base)
            o.append('<path d="%s" fill="url(#%s)" stroke="%s" stroke-width="1.5"/>' % (d, pid, c))
        elif s.get('mode') == 'line' and len(pts) > 1:
            o.append('<path d="M%s" fill="none" stroke="%s" stroke-width="2"/>'
                     % (' L'.join('%.1f %.1f' % (X(x), Y(y)) for x, y in pts), c))
        else:
            sizes = s.get('size', 3)
            hi = s.get('highlight')
            labs = s.get('labels')       # 31-oct (relay-floors): a label written next to each point
            for i, (x, y) in enumerate(pts):
                r = sizes[i] if isinstance(sizes, list) else sizes
                col = PALETTE[1] if hi and hi[i] else c
                o.append('<circle cx="%.1f" cy="%.1f" r="%.1f" fill="%s" fill-opacity="0.85"/>' % (X(x), Y(y), r, col))
                if labs and i < len(labs) and labs[i]:
                    pos = (s.get('label_pos') or ['above'] * len(labs))[i]
                    dx, dy, anc = {'above': (r + 3, -r - 3, 'start'), 'below': (r + 3, r + 12, 'start'),
                                   'left': (-r - 3, -r - 3, 'end')}.get(pos, (r + 3, -r - 3, 'start'))
                    o.append('<text x="%.1f" y="%.1f" font-size="11" fill="%s" text-anchor="%s" font-weight="bold" '
                             'paint-order="stroke" stroke="#fff" stroke-width="3">%s</text>'
                             % (X(x) + dx, Y(y) + dy, c, anc, esc(labs[i])))
        if s.get('name'):
            leg.append((c, s['name']))
    o.append('</g>')
    o.append('<text x="%d" y="%d" text-anchor="middle" font-size="12">%s</text>' % (width / 2, height - 8, esc(xlabel)))
    o.append('<text x="14" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 14 %d)">%s</text>'
             % (height / 2, height / 2, esc(ylabel)))
    for k, (c, n) in enumerate(leg):
        lx, ly = L + (k % cols) * (width - L - R) / 2, height + 4 + 16 * (k // cols)
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


def bars(items, title='', xlabel='', width=560, ref=None, ref_label=''):
    """Horizontal bars, already ordered: items = [(label, value, colour or None)]; ``ref``: a vertical reference line
    (e.g. the present value). 31-oct (relay-floors): which hardware change lowers the floor most."""
    if not items:
        return {'kind': 'svg', 'svg': '<svg xmlns="http://www.w3.org/2000/svg"/>', 'title': title}
    L, R, T, row = 210, 60, 26, 24
    H = T + row * len(items) + 34
    vmax = max([v for _, v, _ in items] + ([ref] if ref else [])) * 1.08 or 1
    X = lambda v: L + v / vmax * (width - L - R)
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (width, H)]
    if ref:
        o.append('<line x1="%.1f" x2="%.1f" y1="%d" y2="%d" stroke="#B00020" stroke-dasharray="4 3"/>'
                 % (X(ref), X(ref), T - 4, T + row * len(items)))
        o.append('<text x="%.1f" y="%d" font-size="10" fill="#B00020" text-anchor="middle">%s</text>'
                 % (X(ref), T + row * len(items) + 12, esc(ref_label)))
    for i, (lab, v, col) in enumerate(items):
        y = T + i * row
        o.append('<rect x="%d" y="%d" width="%.1f" height="%d" rx="3" fill="%s"/>'
                 % (L, y + 3, max(X(v) - L, 1), row - 8, col or PALETTE[0]))
        o.append('<text x="%d" y="%d" font-size="11" text-anchor="end">%s</text>' % (L - 6, y + row / 2 + 4, esc(lab)))
        o.append('<text x="%.1f" y="%d" font-size="11" paint-order="stroke" stroke="#fff" stroke-width="4">%.3g</text>'
                 % (X(v) + 4, y + row / 2 + 4, v))          # white halo: readable across the reference line
    o.append('<text x="%d" y="%d" font-size="12" text-anchor="middle">%s</text>' % ((L + width - R) / 2, H - 4, esc(xlabel)))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': title}


def stacked_bars(rows, parts, title='', xlabel='', width=560):
    """Horizontal stacked bars: rows = [(label, label colour, [value per part])], parts = [(name, colour)]. The label
    keeps the colour of its row elsewhere (31-oct, relay-floors: two figures that go together share their colours)."""
    if not rows:
        return {'kind': 'svg', 'svg': '<svg xmlns="http://www.w3.org/2000/svg"/>', 'title': title}
    L, R, T, row = 200, 70, 26, 26
    H = T + row * len(rows) + 52 + 16 * ((len(parts) + 1) // 2)
    vmax = max(sum(r[2]) for r in rows) * 1.05 or 1
    R = 150 if any(len(r) > 3 for r in rows) else R
    X = lambda v: v / vmax * (width - L - R)
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (width, H)]
    for i, rw in enumerate(rows):
        lab, lc, vals = rw[:3]
        note = rw[3] if len(rw) > 3 else None
        y, x = T + i * row, L
        o.append('<text x="%d" y="%d" font-size="11" text-anchor="end" fill="%s" font-weight="bold">%s</text>'
                 % (L - 6, y + row / 2 + 4, lc or '#333', esc(lab)))
        for (pname, pc), v in zip(parts, vals):
            w = X(v)
            o.append('<rect x="%.1f" y="%d" width="%.1f" height="%d" fill="%s"><title>%s: %.3g</title></rect>'
                     % (x, y + 4, max(w, 0), row - 9, pc, esc(pname), v))
            x += w
        o.append('<text x="%.1f" y="%d" font-size="11">%s</text>'
                 % (x + 4, y + row / 2 + 4, esc(note) if note else _tick(sum(vals))))
    ly = T + row * len(rows) + 14
    for k, (pname, pc) in enumerate(parts):      # 31-oct: two legend entries per line (they overlapped on one line)
        lx = 20 + (k % 2) * (width - 40) / 2
        yy = ly + 16 * (k // 2)
        o.append('<rect x="%.1f" y="%d" width="12" height="9" fill="%s"/><text x="%.1f" y="%d" font-size="11">%s</text>'
                 % (lx, yy, pc, lx + 16, yy + 9, esc(pname)))
    o.append('<text x="%d" y="%d" font-size="12" text-anchor="middle">%s</text>' % ((L + width - R) / 2, H - 6, esc(xlabel)))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': title}


def row(plots, width=1100, gap=10):
    """Several small SVG figures side by side in one SVG (31-oct, relay-floors: panels compared at a glance).
    Each plot keeps its own viewBox; the row scales as a whole."""
    import re as _re
    boxes = []
    for p in plots:
        m = _re.search(r'viewBox="0 0 ([0-9.]+) ([0-9.]+)"', p['svg'])
        boxes.append((float(m.group(1)), float(m.group(2))) if m else (560.0, 320.0))
    H = max(h for _, h in boxes) + 22
    W = sum(w for w, _ in boxes) + gap * (len(boxes) - 1)
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (W, H)]
    x = 0
    for p, (w, h) in zip(plots, boxes):
        o.append('<text x="%.1f" y="14" font-size="13" text-anchor="middle" font-weight="bold">%s</text>'
                 % (x + w / 2, esc(p.get('title', ''))))
        inner = p['svg'].replace('<svg ', '<svg x="%.1f" y="20" width="%.1f" height="%.1f" ' % (x, w, h), 1)
        o.append(inner)
        x += w + gap
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': ''}


def table(head, rows):
    return {'head': [str(h) for h in head], 'rows': [[str(x) for x in r] for r in rows]}


def result(text='', plots=(), table=None):
    out = {'text': text, 'plots': list(plots)}
    if table:
        out['table'] = table
    return json.dumps(out)


def error(msg):
    return json.dumps({'error': msg})
