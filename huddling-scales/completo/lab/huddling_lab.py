# encaje: laboratorio del blueprint huddling-scales (corre en el navegador con Pyodide; Python puro, sin dependencias).
"""Labs of «Huddling, diatonic and pentatonic scales in Z12»: Figures 1 and 2 of the paper, live.

run_clocks: Figure 1. A set A ⊆ Z12, a unit u and a shift s: the clocks of A and of T_s M_u A, the Fourier magnitudes
|Â(t)| of both (M_u permutes the frequencies: the transform of M_uA at t is Â(ut)), and a torus on which every pitch
class sits at once on the chromatic circle (long way round) and on the circle of fifths (short way round): M_5 swaps
the two circles, which is why the chromatic cluster C_7 becomes the diatonic set.
run_cloud: Figure 2. All k-note sets, as points (S_1, S_5, E_V) with V(j) = (7-j)^p: the arcs and the diatonic orbit
are the extreme points; a slider moves the exponent p of the potential."""
import cmath
import itertools
import json
import math

N = 12


def dft(A, t):
    return sum(cmath.exp(-2j * math.pi * a * t / N) for a in A)


def parse_set(text):
    out = sorted({int(x) % N for x in str(text).replace(';', ',').replace(' ', ',').split(',') if x.strip() != ''})
    return out


def clock_svg(A, colour, title, cx, path_order=None):
    R = 70
    o = ['<g>', '<text x="%d" y="18" text-anchor="middle" font-size="13">%s</text>' % (cx, title),
         '<circle cx="%d" cy="105" r="%d" fill="none" stroke="#bbb"/>' % (cx, R)]
    pts = {}
    for p in range(N):
        ang = math.pi / 2 - 2 * math.pi * p / N
        x, y = cx + R * math.cos(ang), 105 - R * math.sin(ang)
        pts[p] = (x, y)
        on = p in A
        o.append('<circle cx="%.1f" cy="%.1f" r="%s" fill="%s" stroke="#888"/>' % (x, y, 6 if on else 3.5,
                                                                                  colour if on else '#fff'))
        lx, ly = cx + (R + 15) * math.cos(ang), 105 - (R + 15) * math.sin(ang)
        o.append('<text x="%.1f" y="%.1f" text-anchor="middle" font-size="11">%d</text>' % (lx, ly + 4, p))
    if path_order and len(path_order) > 1:
        d = 'M' + ' L'.join('%.1f %.1f' % pts[p] for p in path_order)
        o.append('<path d="%s" fill="none" stroke="%s" stroke-dasharray="4 3"/>' % (d, colour))
    o.append('</g>')
    return ''.join(o)


def run_clocks(params):
    p = json.loads(params)
    A = parse_set(p.get('set', '0,1,2,3,4,5,6'))
    u, s = int(p.get('u', 5)) % N, int(p.get('s', 11)) % N
    if math.gcd(u, N) != 1:
        return json.dumps({'error': 'u must be a unit of Z12: 1, 5, 7 or 11'})
    B = sorted({(u * a + s) % N for a in A})
    # the dashed path: B in the order of repeated addition of u (a chain of fourths/fifths when u = 5 or 7)
    start = min(B, key=lambda b: sum(((b + k * u) % N) in B for k in range(N)) * -1)
    chain = [b for b in ((start + k * u) % N for k in range(N)) if b in B]
    svg = ('<svg viewBox="0 0 560 200" style="max-width:100%;background:#fff" xmlns="http://www.w3.org/2000/svg">'
           + clock_svg(A, '#1B6F8C', 'A = {%s}' % ','.join(map(str, A)), 130)
           + '<text x="280" y="100" text-anchor="middle" font-size="14">→</text>'
           + '<text x="280" y="122" text-anchor="middle" font-size="12">T%d∘M%d</text>' % (s, u)
           + clock_svg(B, '#B5530F', 'T%dM%dA = {%s}' % (s, u, ','.join(map(str, B))), 430, chain) + '</svg>')
    rows = [[t, '%.4f' % abs(dft(A, t)), '%.4f' % abs(dft(B, t)), '%.4f' % abs(dft(A, (u * t) % N))] for t in range(1, 7)]
    # the torus: angle θ = 2πp/12 along the chromatic circle, φ = 2π(7p mod 12)/12 along the circle of fifths
    def tor(p_, r=1.0, Rt=2.4):
        th, ph = 2 * math.pi * p_ / N, 2 * math.pi * ((7 * p_) % N) / N
        return [(Rt + r * math.cos(ph)) * math.cos(th), (Rt + r * math.cos(ph)) * math.sin(th), r * math.sin(ph)]
    grid = [[[(2.4 + math.cos(2 * math.pi * j / 18)) * math.cos(2 * math.pi * i / 36),
              (2.4 + math.cos(2 * math.pi * j / 18)) * math.sin(2 * math.pi * i / 36),
              math.sin(2 * math.pi * j / 18)] for j in range(19)] for i in range(37)]
    items = [{'type': 'surface', 'grid': grid, 'color': '#c9d6e3', 'opacity': 0.25, 'name': 'Z12 on a torus'},
             {'type': 'points', 'points': [tor(a) for a in A], 'color': '#1B6F8C', 'size': 7, 'name': 'A'},
             {'type': 'points', 'points': [tor(b) for b in B], 'color': '#B5530F', 'marker': 'star', 'size': 9,
              'name': 'T_s M_u A'},
             {'type': 'curve', 'points': [tor(p_) for p_ in range(N)] + [tor(0)], 'color': '#888', 'width': 1,
              'name': 'the chromatic circle'}]
    return json.dumps({
        'text': ('|Â(1)| of A = %.4f and |Â(5)| of T_sM_uA = %.4f: M_%d sends frequency 1 to frequency %d. The maximum '
                 '2+√3 = 3.7321 is reached at cardinality 7 exactly on arcs (frequency 1) and on the diatonic orbit '
                 '(frequency 5).' % (abs(dft(A, 1)), abs(dft(B, 5)), u, (u * 1) % N)),
        'plots': [{'kind': 'svg', 'svg': svg, 'figure': 'paperfig-1'},
                  {'kind': '3d', 'title': 'Every pitch class on two circles at once: chromatic (long way) and fifths '
                                         '(short way). M5 swaps them.', 'axes': ['', '', ''], 'items': items}],
        'table': {'head': ['t', '|Â(t)| of A', '|transform| of T_sM_uA', '|Â(u·t)| of A'], 'rows': rows}})


def interval_vector(A):
    iv = [0] * 7
    for a, b in itertools.combinations(A, 2):
        d = (a - b) % N
        iv[min(d, N - d)] += 1
    return iv


def run_cloud(params):
    p = json.loads(params)
    k = max(1, min(11, int(p.get('k', 7))))
    exps = [0.5, 1, 1.5, 2, 3, 4]
    pexp = float(p.get('p', 2))
    if pexp not in exps:
        exps = sorted(set(exps + [pexp]))
    classes = {}
    for A in itertools.combinations(range(N), k):
        s1, s5 = abs(dft(A, 1)) ** 2, abs(dft(A, 5)) ** 2
        iv = tuple(interval_vector(A))
        key = (round(s1, 6), round(s5, 6), iv)
        classes[key] = classes.get(key, 0) + 1
    top5 = max(c[1] for c in classes)

    def energy(iv, e):
        return sum(iv[j] * (7 - j) ** e for j in range(1, 7))
    slider_items = []
    for e in exps:
        pts = [[c[0], c[1], energy(c[2], e)] for c in classes]
        best = [[c[0], c[1], energy(c[2], e)] for c in classes if abs(c[1] - top5) < 1e-6]
        slider_items.append([{'type': 'points', 'points': pts, 'color': '#1B6F8C', 'size': 4, 'opacity': 0.7,
                              'name': '%d classes of %d-note sets' % (len(classes), k)},
                             {'type': 'points', 'points': best, 'color': '#B5530F', 'marker': 'star', 'size': 11,
                              'name': 'maximum of S5'}])
    # the paper's own view (Figure 2): S5 against the energy, marker area by multiplicity, at the chosen p
    xs = [c[1] for c in classes]
    ys = [energy(c[2], pexp) for c in classes]
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    W, H, L, B = 560, 300, 60, 40
    X = lambda v: L + (v - x0) / ((x1 - x0) or 1) * (W - L - 16)
    Y = lambda v: H - B - (v - y0) / ((y1 - y0) or 1) * (H - B - 20)
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (W, H)]
    for c, x, y in zip(classes, xs, ys):
        r = 2.5 + 1.6 * math.sqrt(classes[c])
        star = abs(c[1] - top5) < 1e-6
        o.append('<circle cx="%.1f" cy="%.1f" r="%.1f" fill="%s" fill-opacity="0.6"/>' % (
            X(x), Y(y), r, '#B5530F' if star else '#1B6F8C'))
    o.append('<text x="%d" y="%d" text-anchor="middle" font-size="12">S5 = |Â(5)|²</text>' % (W / 2, H - 8))
    o.append('<text x="14" y="%d" font-size="12" transform="rotate(-90 14 %d)" text-anchor="middle">E_V, V(j)=(7−j)^%g'
             '</text>' % (H / 2, H / 2, pexp))
    o.append('</svg>')
    return json.dumps({
        'text': ('%d sets of %d notes form %d classes (S1, S5, interval vector). Orange: the maximum of S5 (%s sets). '
                 'For k = 7 they are the twelve diatonic transpositions. Move p: V(j) = (7−j)^p is strictly convex '
                 'only for p > 1, and only then are they exactly the minimum of the energy (12 sets; 313 at p = 2, '
                 'as in the paper). At p = 1 (convex, not strictly) the minimum is shared by 252 sets: why the paper '
                 'needs strictness. At p = 0.5 (not convex) 24 other sets have lower energy.'
                 % (sum(classes.values()), k, len(classes), sum(v for c, v in classes.items()
                                                             if abs(c[1] - top5) < 1e-6))),
        'plots': [{'kind': 'svg', 'svg': ''.join(o), 'figure': 'paperfig-2'},
                  {'kind': '3d', 'title': 'All %d-note classes in (S1, S5, energy); slide the exponent p' % k,
                   'axes': ['S1', 'S5', 'E_V'], 'items': [],
                   'slider': {'label': 'p (V(j) = (7−j)^p)', 'values': exps, 'items': slider_items}}]})
