# encaje: lab de un blueprint (lo ejecuta excovery.lemmario.labs en el navegador); no es herramienta: datos de un paper
"""Labs of «Integer frieze patterns and Tabachnikov's four sign changes» (Python in the browser and locally).

run_family: Figures 4 and 5 live. The two lattice polygons A(t), B(t) of Theorem B (closed form of §5), the row
            k = ⌊w/2⌋ of both frieze patterns as determinants, and the differences d_i: bars for the chosen t, and the
            whole family t = 0..T in 3D (signed log height), the negative entries marked.
run_pair:   your own pair. Two quiddities and a row k: is each one an integer Conway–Coxeter frieze pattern (the
            continuants close with a row of 1s and a row of 0s, all entries positive)? The difference of row k and its
            sign changes in the three readings of the note (s⁻ zeros deleted, s⁺ zeros signed at best, E), the two
            triangulations (Figure 2 live), and the two frieze patterns as relief maps in 3D, row k marked.
Exact integer arithmetic throughout (continuants and 2×2 determinants)."""
import json
import math

BLUE, RED, ORANGE, GREY = '#2a78d6', '#e34948', '#B5530F', '#888888'


# ------------------------------------------------------------------------------------------- frieze arithmetic
def K(seq):
    p, c = 0, 1
    for x in seq:
        p, c = c, x * c - p
    return c


def row(q, k):
    """The paper's row k, from i = 0: v_{i,i+k+1} = K(a_{i+1}, ..., a_{i+k}) (§3 of the note)."""
    n = len(q)
    return [K([q[(i + 1 + t) % n] for t in range(k)]) for i in range(n)]


def check_frieze(q):
    """None if q is the quiddity of an integer Conway–Coxeter frieze pattern, else the reason."""
    n = len(q)
    if n < 3:
        return 'needs at least 3 entries'
    if any(x < 1 for x in q):
        return 'entries must be positive integers'
    w = n - 3
    for k in range(1, w + 1):
        r = row(q, k)
        if min(r) <= 0:
            return 'row %d has a non-positive entry (%d)' % (k, min(r))
    if row(q, w + 1) != [1] * n or row(q, w + 2) != [0] * n:
        return 'the pattern does not close (rows %d and %d must be all 1s and all 0s)' % (w + 1, w + 2)
    return None


def changes(d):
    """(s⁻, s⁺, E) of a cyclic integer sequence that is not identically zero."""
    n = len(d)
    nz = [x for x in d if x]
    sm = sum(nz[i] * nz[(i + 1) % len(nz)] < 0 for i in range(len(nz))) if len(nz) > 1 else 0
    E = sum(d[i] * d[(i + 1) % n] <= 0 for i in range(n))
    idx = [i for i in range(n) if d[i]]
    sp = 0
    for t, i in enumerate(idx):
        j = idx[(t + 1) % len(idx)]
        r = n - 1 if len(idx) == 1 else (j - i - 1) % n
        diff = (d[i] > 0) != (d[j] > 0)
        sp += r + 1 if (r + 1) % 2 == diff else r
    return sm, sp, E


def triangulation(q):
    alive = list(range(len(q)))
    a = dict(zip(alive, q))
    diags = []
    while len(alive) > 3:
        for idx, v in enumerate(alive):
            if a[v] == 1:
                u, x = alive[idx - 1], alive[(idx + 1) % len(alive)]
                diags.append((u, x))
                a[u] -= 1
                a[x] -= 1
                alive.pop(idx)
                break
        else:
            return None
    return diags


# ------------------------------------------------------------------------------------------- Theorem B family
def VA(t):
    return ([(1, 0), (0, 1), (-1, 2)] + [(-(t + 2 - s), 2 * (t + 2 - s) - 1) for s in range(t + 1)]
            + [(-3, 4), (-4, 5), (-9, 11), (-5, 6), (-11, 13)]
            + [(-6 - 11 * (t + 1 - s), 7 + 13 * (t + 1 - s)) for s in range(t + 1)]
            + [(-6, 7), (-7, 8), (-8, 9), (-9, 10), (-1, 1)])


def VB(t):
    return ([(1, 0), (0, 1), (-1, 3)] + [(-(t + 1 - s), 3 * (t + 1 - s) - 1) for s in range(t + 1)]
            + [(-1, 1), (-2, 1), (-5, 2), (-18, 7), (-13, 5)]
            + [(-8 - 13 * (t - s), 3 + 5 * (t - s)) for s in range(t + 1)]
            + [(-3, 1), (-7, 2), (-11, 3), (-15, 4), (-4, 1)])


def det(u, v):
    return u[0] * v[1] - u[1] * v[0]


def entries(V):
    """Row k = h − 1 of the frieze pattern of V (n = 2h + 1), as a cyclic sequence (§5 of the note)."""
    h = (len(V) - 1) // 2
    return [det(V[i], V[i + h]) if i <= h else det(V[i - h - 1], V[i]) for i in range(len(V))]


def family_d(t):
    return [y - x for x, y in zip(entries(VA(t)), entries(VB(t)))]


def slog(v):
    return math.copysign(math.log10(1 + abs(v)), v)


# ------------------------------------------------------------------------------------------- SVG helpers
def bars_svg(d, title, labels_all=True):
    n = len(d)
    W, H = 640, 260
    pad, bw = 30, (640 - 60) / n
    top = max(max(d), 1)
    bot = min(min(d), 0)
    scale = (H - 70) / (top - bot) if top > bot else 1
    y0 = 40 + top * scale
    o = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 %d %d" font-family="serif" font-size="11">' % (W, H),
         '<text x="%d" y="18" font-size="13">%s</text>' % (pad, title),
         '<line x1="%d" y1="%.1f" x2="%d" y2="%.1f" stroke="#999"/>' % (pad - 4, y0, W - pad + 4, y0)]
    for i, v in enumerate(d):
        x = pad + i * bw
        h = v * scale
        col = BLUE if v > 0 else RED if v < 0 else GREY
        yt = y0 - h if v > 0 else y0
        o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" rx="1.5" fill="%s"><title>d_%d = %d</title></rect>'
                 % (x + 1, yt, max(bw - 2, 1), max(abs(h), 1.5), col, i, v))
        if labels_all or v < 0:
            ly = (y0 - h - 4) if v > 0 else (y0 - h + 12)
            o.append('<text x="%.1f" y="%.1f" text-anchor="middle" font-size="9">%d</text>' % (x + bw / 2, ly, v))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': title}


def polygon_svg(q, cx, label):
    n = len(q)
    r = 95
    pts = [(cx + r * math.sin(2 * math.pi * i / n), 120 - r * math.cos(2 * math.pi * i / n)) for i in range(n)]
    o = ['<polygon points="%s" fill="none" stroke="#222" stroke-width="1.6"/>' % ' '.join('%.1f,%.1f' % p for p in pts)]
    for u, v in triangulation(q) or []:
        o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#555"/>' % (pts[u] + pts[v]))
    for i, p in enumerate(pts):
        lx, ly = cx + 1.16 * (p[0] - cx), 120 + 1.16 * (p[1] - 120)
        o.append('<circle cx="%.1f" cy="%.1f" r="2"/><text x="%.1f" y="%.1f" font-size="9" text-anchor="middle" '
                 'dominant-baseline="middle">%d</text>' % (p[0], p[1], lx, ly, i))
    o.append('<text x="%d" y="236" text-anchor="middle" font-size="12">%s</text>' % (cx, label))
    return ''.join(o)


# ------------------------------------------------------------------------------------------- the labs
def run_family(params):
    p = json.loads(params)
    t = max(0, min(30, int(p.get('t', 5))))
    T = max(t, 8)
    d = family_d(t)
    n = len(d)
    neg = [i for i in range(n) if d[i] < 0]
    sm, sp, E = changes(d)
    items = []
    for tt in range(T + 1):
        dd = family_d(tt)
        pts = [[i - (tt + 8), tt, slog(v)] for i, v in enumerate(dd)]
        items.append({'type': 'curve', 'points': pts, 'color': ORANGE if tt == t else BLUE,
                      'width': 3 if tt == t else 1.5, 'name': 't = %d' % tt if tt in (0, t, T) else ''})
        items.append({'type': 'points', 'points': [pt for pt, v in zip(pts, dd) if v < 0], 'color': RED, 'size': 6,
                      'name': 'd < 0' if tt == 0 else ''})
    items.append({'type': 'curve', 'points': [[-(T + 8), 0, 0], [T + 6, 0, 0]], 'color': '#444', 'name': 'd = 0'})
    return json.dumps({
        'text': ('t = %d: n = %d, row k = %d = ⌊w/2⌋. The differences d_i = r_k(b)_i − r_k(a)_i have no zero and '
                 '%d sign changes (s⁻ = s⁺ = E = %d). Negative entries: %s. For t ≥ 5 there is exactly one, '
                 'd_{t+8} = 5 − 13 = −8; for t ≤ 4 also d_{t+9} = 2t − 9. The 3D view shows t = 0..%d '
                 '(height sign(d)·log₁₀(1 + |d|)), centred at the negative entry; your t in orange.'
                 % (t, n, (n - 3) // 2, sm, sm, ', '.join('d_%d = %d' % (i, d[i]) for i in neg), T)),
        'plots': [dict(bars_svg(d, 'd_i for t = %d (n = %d)' % (t, n), labels_all=n <= 21), figure='paperfig-4'),
                  {'kind': '3d', 'title': 'the family: one column stays negative', 'axes': ['i − (t+8)', 't', 'sign·log₁₀(1+|d|)'],
                   'items': items, 'figure': 'paperfig-5', 'max_width': 1000}]})


def parse(s):
    return [int(x) for x in s.replace('(', ' ').replace(')', ' ').replace(',', ' ').split()]


def run_pair(params):
    p = json.loads(params)
    try:
        a, b = parse(p.get('a', '')), parse(p.get('b', ''))
    except ValueError:
        return json.dumps({'text': 'Write each quiddity as integers separated by commas.', 'plots': []})
    if len(a) != len(b):
        return json.dumps({'text': 'The two quiddities must have the same length (same width).', 'plots': []})
    if len(a) > 40:
        return json.dumps({'text': 'At most 40 entries in this lab.', 'plots': []})
    for name, q in (('a', a), ('b', b)):
        why = check_frieze(q)
        if why:
            return json.dumps({'text': '%s is not an integer Conway–Coxeter frieze pattern: %s.' % (name, why),
                               'plots': []})
    n = len(a)
    w = n - 3
    k = max(1, min(w, int(p.get('k', (w + 1) // 2))))
    ra, rb = row(a, k), row(b, k)
    d = [y - x for x, y in zip(ra, rb)]
    if not any(d):
        return json.dumps({'text': 'Row %d is the same in both frieze patterns: there is nothing to count.' % k,
                           'plots': []})
    sm, sp, E = changes(d)
    verdict = 'at least four in every reading' if sm >= 4 else \
        ('fewer than four in every reading' if E < 4 else 'fewer than four only if zeros are ignored')
    tri = ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 520 250" font-family="serif">'
           + polygon_svg(a, 130, 'a') + polygon_svg(b, 390, 'b') + '</svg>')
    surf = []
    for name, q, col in (('a', a, BLUE), ('b', b, ORANGE)):
        grid = [[[i, kk, math.log10(v)] for i, v in enumerate(row(q, kk))] for kk in range(1, w + 1)]
        surf.append({'type': 'surface', 'grid': grid, 'color': col, 'opacity': 0.55, 'name': 'frieze %s' % name})
        surf.append({'type': 'curve', 'points': [[i, k, math.log10(v)] for i, v in enumerate(row(q, k))],
                     'color': col, 'width': 4, 'name': 'row %d of %s' % (k, name)})
    return json.dumps({
        'text': ('Both are integer frieze patterns of width %d (n = %d). Row %d: a = %s, b = %s, d = %s. Sign '
                 'changes: s⁻ = %d (zeros deleted), s⁺ = %d (zeros signed at best), E = %d: %s.'
                 % (w, n, k, ra, rb, d, sm, sp, E, verdict)),
        'plots': [{'kind': 'svg', 'svg': tri, 'title': 'the two triangulations', 'figure': 'paperfig-2'},
                  bars_svg(d, 'd_i = r_%d(b)_i − r_%d(a)_i' % (k, k), labels_all=n <= 24),
                  {'kind': '3d', 'title': 'the two frieze patterns as relief maps (height log₁₀ of the entry); row %d '
                   'thick' % k, 'axes': ['position i', 'row', 'log₁₀ entry'], 'items': surf, 'max_width': 1000}]})


if __name__ == '__main__':  # local controls (known values from the note)
    assert family_d(5)[13] == -8 and changes(family_d(5)) == (2, 2, 2)
    assert all(changes(family_d(t))[0] == 2 and 0 not in family_d(t) for t in range(0, 12))
    a14 = [1, 2, 2, 2, 2, 3, 1, 3, 2, 2, 2, 2, 1, 11]
    b14 = [1, 5, 2, 3, 1, 2, 5, 4, 1, 2, 2, 4, 2, 2]
    assert check_frieze(a14) is None and check_frieze(b14) is None
    assert min(y - x for x, y in zip(row(a14, 6), row(b14, 6))) > 0
    r = json.loads(run_pair(json.dumps({'a': '1,2,2,2,2,3,1,4,2,1,4,2,2,1,10', 'b': '4,3,1,2,3,3,4,1,2,2,5,2,2,1,4',
                                        'k': '6'})))
    assert 's⁻ = 2' in r['text'] and 'E = 2' in r['text'], r['text']
    r8 = json.loads(run_pair(json.dumps({'a': '1,2,2,3,3,2,1,3,4,1,5', 'b': '1,3,1,5,4,1,2,2,3,2,3', 'k': '3'})))
    assert 'only if zeros are ignored' in r8['text'], r8['text']
    bad = json.loads(run_pair(json.dumps({'a': '1,2,2,2,2,3,1,4,2,1,4,2,2,2,10', 'b': '4,3,1,2,3,3,4,1,2,2,5,2,2,1,4'})))
    assert 'not an integer' in bad['text'], bad['text']  # control: a wrong quiddity is rejected
    r5 = json.loads(run_pair(json.dumps({'a': '1,2,2,2,2,3,1,4,2,1,4,2,2,1,10', 'b': '4,3,1,2,3,3,4,1,2,2,5,2,2,1,4',
                                         'k': '5'})))
    assert 'at least four' in r5['text'] or 'only if zeros' in r5['text'], r5['text']  # row 5: no counterexample
    print('controls: OK |', r['text'][:120])
    print(r5['text'][:200])
