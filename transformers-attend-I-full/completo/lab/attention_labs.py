"""Pure-Python browser labs for exact finite formulas in Part I."""

import json
import math
import random


def _number(value, label, lo, hi):
    try:
        x = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{label}: enter a number") from exc
    if not math.isfinite(x) or not lo <= x <= hi:
        raise ValueError(f"{label}: use a value in [{lo}, {hi}]")
    return x


def _integer(value, label, lo, hi):
    x = _number(value, label, lo, hi)
    if x != int(x):
        raise ValueError(f"{label}: enter an integer")
    return int(x)


def _plot(curves, x_min, x_max, y_min, y_max, labels, marker=None):
    """Small dependency-free SVG; curves are [(points, colour, dashed)]."""
    width, height, left, top, span_x, span_y = 640, 270, 54, 20, 550, 205
    sx = lambda x: left + span_x * (x - x_min) / (x_max - x_min)
    sy = lambda y: top + span_y * (y_max - y) / (y_max - y_min)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
           'style="max-width:100%;background:#fff;font-family:system-ui">',
           f'<path d="M {left} {top} V {top+span_y} H {left+span_x}" fill="none" stroke="#555"/>']
    for value in (y_min, (y_min + y_max) / 2, y_max):
        y = sy(value)
        out.append(f'<path d="M {left} {y:.2f} H {left+span_x}" stroke="#e3e8ee"/>')
        out.append(f'<text x="{left-7}" y="{y+4:.2f}" text-anchor="end" font-size="11">{value:.2f}</text>')
    for points, colour, dashed in curves:
        poly = ' '.join(f'{sx(x):.2f},{sy(y):.2f}' for x, y in points)
        dash = ' stroke-dasharray="6 4"' if dashed else ''
        out.append(f'<polyline points="{poly}" fill="none" stroke="{colour}" stroke-width="2.3"{dash}/>')
    if marker is not None:
        x, y = marker
        out.append(f'<circle cx="{sx(x):.2f}" cy="{sy(y):.2f}" r="5" fill="#ad3f1d"/>')
    out += [f'<text x="{left+span_x/2}" y="{height-9}" text-anchor="middle" font-size="12">{labels[0]}</text>',
            f'<text x="{left+span_x+4}" y="{top+13}" text-anchor="end" font-size="12">{labels[1]}</text>',
            '</svg>']
    return ''.join(out)


def cycle_count(m, theta, d):
    """Equation (4.2): equality at the cycle threshold counts as cycled."""
    x = m * math.log(d / (2 * math.pi)) / math.log(theta)
    cycled = min(m, max(0, 1 + math.floor(x)))
    return m - cycled


def cycle_continuous(m, theta, d):
    x = 1 - math.log(d / (2 * math.pi)) / math.log(theta)
    return min(1.0, max(0.0, x))


def _cycles_3d(m, theta, d, dmax):
    """Exact uncycled fraction over distance and RoPE base, not attention."""
    xmax = math.log10(dmax)
    selected_base = math.log10(theta)
    ymin = min(3.0, selected_base)
    ymax = max(6.0, selected_base + 0.01)
    grid = []
    for j in range(17):
        log_base = ymin + (ymax - ymin) * j / 16
        base = 10 ** log_base
        grid.append([[xmax * i / 40, log_base,
                      cycle_count(m, base, 10 ** (xmax * i / 40)) / m]
                     for i in range(41)])
    return {'kind': '3d', 'figure': 'paperfig-2',
            'title': 'Exact uncycled fraction: distance × RoPE base (geometric count only)',
            'axes': ['log10 distance', 'log10 base', 'uncycled / m'],
            'items': [
                {'type': 'surface', 'name': 'exact fraction', 'grid': grid,
                 'color': '#176d91', 'opacity': 0.65},
                {'type': 'points', 'name': 'selected values', 'marker': 'star',
                 'points': [[math.log10(d), selected_base,
                             cycle_count(m, theta, d) / m]],
                 'color': '#bd542b', 'size': 8}]}


def run_cycles(params):
    try:
        p = json.loads(params)
        m = _integer(p.get('m', 32), 'planes', 1, 128)
        theta = _number(p.get('theta', 10000), 'RoPE base', 1.000001, 1000000)
        d = _number(p.get('d', 2000), 'distance', 0.001, 1000000)
        dmax = _number(p.get('dmax', 100000), 'plot maximum', 10, 1000000)
        if d > dmax:
            raise ValueError('distance must not exceed plot maximum')
        xs = [10 ** (i * math.log10(dmax) / 179) for i in range(180)]
        exact = [(math.log10(x), cycle_count(m, theta, x) / m) for x in xs]
        smooth = [(math.log10(x), cycle_continuous(m, theta, x)) for x in xs]
        n = cycle_count(m, theta, d)
        svg = _plot([(exact, '#176d91', False), (smooth, '#c26423', True)],
                    0, math.log10(dmax), 0, 1, ('log10(distance)', 'uncycled fraction'),
                    (math.log10(d), n / m))
        rows = [[f'{x:g}', cycle_count(m, theta, x), m-cycle_count(m, theta, x),
                 f'{cycle_count(m, theta, x)/m:.4f}'] for x in (10, min(d, dmax), dmax)]
        return json.dumps({'text': f'At d={d:g}, {n} of {m} planes have not completed one cycle. '
                           'Blue: exact count. Dashed orange: clipped continuous approximation. '
                           'A completed cycle does not imply loss of information or attention decay.',
                           'plots': [_cycles_3d(m, theta, d, dmax),
                                     {'kind': 'svg', 'svg': svg}],
                           'table': {'head': ['distance', 'uncycled', 'cycled', 'uncycled/m'], 'rows': rows}})
    except (ValueError, json.JSONDecodeError) as exc:
        return json.dumps({'error': str(exc)})


def random_cycles():
    dmax = random.choice((10000, 100000, 1000000))
    return json.dumps({'m': random.choice((16, 32, 64)), 'theta': random.choice((1000, 10000, 100000)),
                       'd': random.choice((100, 1000, 2000, 10000)), 'dmax': dmax})


def pade_candidate(theta, context):
    scale = math.sqrt(2) * context
    return (2 * theta - scale) / (2 * theta + scale)


def _pade_3d(theta, context):
    """The stipulated candidate over base and context, not measured exponents."""
    selected_base = math.log10(theta)
    selected_context = math.log10(context)
    xmin = min(3.0, selected_base)
    xmax = max(6.0, selected_base + 0.01)
    grid = []
    for j in range(21):
        log_context = 6 * j / 20
        T = 10 ** log_context
        grid.append([[xmin + (xmax - xmin) * i / 30, log_context,
                      pade_candidate(10 ** (xmin + (xmax - xmin) * i / 30), T)]
                     for i in range(31)])
    return {'kind': '3d', 'figure': 'paperfig-5',
            'title': 'Historical Padé candidate over base × context (unvalidated)',
            'axes': ['log10 base', 'log10 context', 'candidate exponent'],
            'items': [
                {'type': 'surface', 'name': 'candidate formula', 'grid': grid,
                 'color': '#176d91', 'opacity': 0.65},
                {'type': 'points', 'name': 'selected values', 'marker': 'star',
                 'points': [[selected_base, selected_context,
                             pade_candidate(theta, context)]],
                 'color': '#bd542b', 'size': 8}]}


def run_pade(params):
    try:
        p = json.loads(params)
        theta = _number(p.get('theta', 10000), 'RoPE base', 1.000001, 1000000)
        context = _number(p.get('T', 2000), 'context T', 1, 1000000)
        gamma = pade_candidate(theta, context)
        xs = [3 + 3 * i / 119 for i in range(120)]
        curve = [(x, pade_candidate(10**x, context)) for x in xs]
        svg = _plot([(curve, '#176d91', False)], 3, 6, -1, 1,
                    ('log10(RoPE base)', 'candidate exponent'),
                    (math.log10(theta), gamma) if 1000 <= theta <= 1000000 else None)
        return json.dumps({'text': f'For base {theta:g} and context {context:g}, the historical '
                           f'Padé candidate is {gamma:.6f}; its algebraic zero occurs at '
                           f'T=sqrt(2)·base={math.sqrt(2)*theta:.3f}. The curve is a stipulated '
                           'formula, not a derivation from the RoPE cosine sum and not a validated '
                           'prediction of trained attention.',
                           'plots': [_pade_3d(theta, context),
                                     {'kind': 'svg', 'svg': svg}],
                           'table': {'head': ['base', 'T', 'candidate exponent'],
                                     'rows': [[f'{t:g}', f'{context:g}', f'{pade_candidate(t,context):.6f}']
                                              for t in (theta, 10000, 100000)]}})
    except (ValueError, json.JSONDecodeError) as exc:
        return json.dumps({'error': str(exc)})


def random_pade():
    return json.dumps({'theta': random.choice((1000, 10000, 100000, 500000)),
                       'T': random.choice((512, 2000, 4096, 16384))})


def continuous_quantile(n, f, g):
    a = 1 - g
    ln = math.log(n)
    if abs(a) < 1e-10:
        return math.exp(f * ln)
    return math.exp(math.log1p(f * math.expm1(a * ln)) / a)


def discrete_quantile(n, f, g):
    weights = [math.exp(-g * math.log(d)) for d in range(1, n + 1)]
    target = f * math.fsum(weights)
    mass = 0.0
    for i, weight in enumerate(weights, 1):
        mass += weight
        if mass >= target:
            return i
    return n


def run_quantiles(params):
    try:
        p = json.loads(params)
        n = _integer(p.get('N', 2000), 'support N', 2, 5000)
        f = _number(p.get('f', 0.9), 'mass fraction f', 0.000001, 0.999999)
        g = _number(p.get('g', 0.674), 'exponent g', -2, 3)
        dc = continuous_quantile(n, f, g)
        dd = discrete_quantile(n, f, g)
        gs = [-0.5 + i * 2.5 / 59 for i in range(60)]
        c = [(x, continuous_quantile(n, f, x) / n) for x in gs]
        q = [(x, discrete_quantile(n, f, x) / n) for x in gs]
        svg = _plot([(c, '#176d91', False), (q, '#c26423', True)],
                    -0.5, 2, 0, 1, ('exponent g', 'quantile/N'), (g, dc / n) if -0.5 <= g <= 2 else None)
        return json.dumps({'text': f'For N={n}, f={f:g}, g={g:g}: continuous quantile {dc:.3f}; '
                           f'discrete token quantile {dd}. The blue continuous curve and dashed '
                           'orange integer curve use different measures. These are family calculations, '
                           'not a validated KV-cache policy.',
                           'plots': [{'kind': 'svg', 'svg': svg, 'figure': 'paperfig-12'}],
                           'table': {'head': ['g', 'continuous', 'discrete'],
                                     'rows': [[f'{x:.3f}', f'{continuous_quantile(n,f,x):.3f}',
                                               discrete_quantile(n,f,x)] for x in (g, 1.0, 1.5)]}})
    except (ValueError, json.JSONDecodeError, OverflowError) as exc:
        return json.dumps({'error': str(exc)})


def random_quantiles():
    return json.dumps({'N': random.choice((100, 500, 2000)), 'f': random.choice((0.5, 0.9, 0.95)),
                       'g': random.choice((0.5, 0.75, 1.0, 1.25))})


def softmax(values):
    peak = max(values)
    weights = [math.exp(x - peak) for x in values]
    total = math.fsum(weights)
    return [x / total for x in weights]


def _vector(value, label):
    try:
        out = [float(x.strip()) for x in str(value).split(',')]
    except ValueError as exc:
        raise ValueError(f'{label}: use comma-separated numbers') from exc
    if not 2 <= len(out) <= 12 or not all(math.isfinite(x) and abs(x) <= 100 for x in out):
        raise ValueError(f'{label}: use 2–12 finite numbers of magnitude at most 100')
    return out


def run_softmax(params):
    try:
        p = json.loads(params)
        scores = _vector(p.get('scores', '0.75,0'), 'scores')
        errors = _vector(p.get('errors', '0,1.5'), 'errors')
        if len(scores) != len(errors):
            raise ValueError('scores and errors need the same number of entries')
        q = softmax(scores)
        changed = softmax([s + e for s, e in zip(scores, errors)])
        tv = math.fsum(abs(a-b) for a, b in zip(q, changed)) / 2
        omega = max(errors) - min(errors)
        bound = math.tanh(omega / 4)
        barw = 500 / len(q)
        bars = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 260" '
                'style="max-width:100%;background:#fff;font-family:system-ui">']
        for i, (a, b) in enumerate(zip(q, changed)):
            x = 55 + i * barw
            bars.append(f'<rect x="{x:.1f}" y="{220-170*a:.1f}" width="{barw*.38:.1f}" '
                        f'height="{170*a:.1f}" fill="#176d91"/>')
            bars.append(f'<rect x="{x+barw*.4:.1f}" y="{220-170*b:.1f}" width="{barw*.38:.1f}" '
                        f'height="{170*b:.1f}" fill="#c26423"/>')
            bars.append(f'<text x="{x+barw*.39:.1f}" y="240" text-anchor="middle" font-size="11">{i+1}</text>')
        bars.append('<text x="60" y="18" font-size="12" fill="#176d91">blue: original</text>'
                    '<text x="190" y="18" font-size="12" fill="#c26423">orange: changed</text></svg>')
        return json.dumps({'text': f'TV={tv:.6f}; sharp universal bound tanh(oscillation/4)='
                           f'{bound:.6f}; score-error oscillation={omega:.6f}. '
                           'A common score shift cancels. The inequality concerns a fixed finite row.',
                           'plots': [{'kind': 'svg', 'svg': ''.join(bars)}],
                           'table': {'head': ['key', 'original', 'changed', 'score error'],
                                     'rows': [[i+1, f'{a:.6f}', f'{b:.6f}', f'{e:.3f}']
                                              for i, (a,b,e) in enumerate(zip(q, changed, errors))]}})
    except (ValueError, json.JSONDecodeError) as exc:
        return json.dumps({'error': str(exc)})


def random_softmax():
    n = random.choice((2, 3, 5))
    return json.dumps({'scores': ','.join(str(random.randint(-2,2)) for _ in range(n)),
                       'errors': ','.join(str(random.randint(-2,2)) for _ in range(n))})
