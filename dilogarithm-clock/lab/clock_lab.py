# encaje: lab de un blueprint (lo ejecuta excovery.lemmario.labs en el navegador); no es herramienta: datos de un paper
"""Labs of «The Clock That Never Ticks»: Figures 2 and 3 of the paper, live (Python in the browser).

run_clausen: the Fejér–Jackson partial sums S_M(θ) as a surface over (θ, M), and Cl₂ with its bound sin(θ)/2.
run_clock:   the autocorrelation S(θ) of the state p_n ∝ n^(−s) as a curve (θ, Re S, Im S), against the two-level
             state; the floor |S| ≥ |S(π)| for every s (the antipode floor; for s = 2 it is the paper's |S| ≥ 1/2).
Series are truncated at n ≤ NMAX (tail ≲ NMAX^(1−s)); the paper's own figures use mpmath at 30–40 digits.
"""
import json
import math

NMAX = 3000


def fejer(M, t):
    return sum(math.sin(k * t) / k for k in range(1, M + 1))


def clausen(t, N=NMAX):
    return sum(math.sin(n * t) / (n * n) for n in range(1, N + 1))


def run_clausen(params):
    p = json.loads(params)
    Mmax = max(1, min(40, int(p.get('M', 12))))
    ts = [2 * math.pi * i / 120 for i in range(1, 120)]
    grid = [[[t, M, fejer(M, t)] for t in ts] for M in range(1, Mmax + 1)]
    # θ = 2π·60/120 is π in floating point minus an ulp, where S_M ≈ 0 ± 1e-16: keep away from the endpoint
    neg_inside = sum(1 for row in grid for t, M, v in row if 1e-9 < t < math.pi - 1e-9 and v <= 0)
    cl = [(t, clausen(t, 800)) for t in ts]
    bound = [(t, math.sin(t) / 2) for t in ts if t < math.pi]
    G = clausen(math.pi / 2)
    ring = [[math.cos(x), math.sin(x), 0] for x in [2 * math.pi * i / 120 for i in range(121)]]
    cl3 = [[math.cos(x), math.sin(x), v] for x, v in cl]
    bound3 = [[math.cos(x), math.sin(x), v] for x, v in bound]
    # what M changes (21-oct, Carles: «cambio el parámetro y no veo que cambie nada»): YOUR M, orange in the 3D
    ts_in = [t for t in ts if 1e-9 < t < math.pi - 1e-9]
    vmin = min(fejer(Mmax, t) for t in ts_in)
    mine = [[t, Mmax, fejer(Mmax, t)] for t in ts]
    return json.dumps({
        'text': ('Fejér–Jackson partial sums S_M(θ) = Σ_{k≤M} sin(kθ)/k for M = 1..%d: on (0, π) the surface stays '
                 'above zero (%d grid points with S_M ≤ 0 there; the theorem says 0); on (π, 2π) it is the mirror '
                 'image. Your M = %d (orange): its minimum on (0, π) is %.4f > 0. Below: Cl₂ wrapped on the unit circle, with the machine-checked bound sin(θ)/2 (dashed) and '
                 'Catalan\'s constant at the quarter circle (star) (series truncated at n ≤ %d).'
                 % (Mmax, neg_inside, Mmax, vmin, NMAX)),
        'plots': [{'kind': '3d', 'title': 'S_M(θ) over (θ, M) for M ≤ %d: positive on (0, π)' % Mmax,
                   'axes': ['θ', 'M', 'S_M'],
                   'items': [{'type': 'surface', 'grid': grid, 'color': '#1B6F8C', 'opacity': 0.7,
                              'name': 'Fejér–Jackson sums'},
                             {'type': 'curve', 'points': mine, 'color': '#B5530F', 'name': 'M = %d' % Mmax}],
                   'figure': 'paperfig-2', 'panel': 'a', 'max_width': 1000},
                  {'kind': '3d', 'title': 'Cl₂ wrapped on the unit circle: (cos θ, sin θ, Cl₂(θ)), above sin(θ)/2 on (0, π)',
                   'axes': ['cos θ', 'sin θ', 'Cl₂'],
                   'items': [{'type': 'curve', 'points': ring, 'color': '#999', 'name': 'the unit circle (height 0)'},
                             {'type': 'curve', 'points': cl3, 'color': '#1B6F8C', 'name': 'Cl₂(θ)'},
                             {'type': 'curve', 'points': bound3, 'color': '#B5530F', 'dash': True,
                              'name': 'sin(θ)/2 (machine-checked bound)'},
                             {'type': 'points', 'points': [[0, 1, G]], 'color': '#B5530F', 'marker': 'star',
                              'size': 11, 'name': 'G = Cl₂(π/2) ≈ %.6f' % G}],
                   'figure': 'paperfig-2', 'panel': 'c', 'max_width': 1000}]})


def autocorrelation(s, t, N=NMAX):
    z = sum(n ** -s for n in range(1, N + 1))
    re = sum(math.cos(n * t) * n ** -s for n in range(1, N + 1)) / z
    im = -sum(math.sin(n * t) * n ** -s for n in range(1, N + 1)) / z
    return re, im


def run_clock(params):
    p = json.loads(params)
    s = min(6.0, max(1.5, float(p.get('s', 2))))
    svals = sorted(set([1.5, 2.0, 3.0, 4.0, s]))
    ts = [2 * math.pi * i / 160 for i in range(1, 160)]
    two = [[t, math.cos(t / 2) ** 2, -math.sin(t) / 2] for t in ts]       # (1 + e^{-iθ})/2
    axis = [[0, 0, 0], [2 * math.pi, 0, 0]]
    ring = [[math.cos(x), math.sin(x), 0] for x in [2 * math.pi * i / 160 for i in range(161)]]
    two_mod = [[math.cos(x), math.sin(x), abs(math.cos(x / 2))] for x in ts]
    slider_items, wrap_items = [], []
    for sv in svals:
        curve = [[x] + list(autocorrelation(sv, x, 1200)) for x in ts]
        slider_items.append([{'type': 'curve', 'points': curve, 'color': '#1B6F8C', 'name': 'p_n ∝ n^-%g' % sv},
                             {'type': 'curve', 'points': two, 'color': '#B5530F', 'name': 'two-level state'},
                             {'type': 'curve', 'points': axis, 'color': '#444', 'name': 'S = 0 (orthogonal)'}])
        mods = [[math.cos(c[0]), math.sin(c[0]), math.hypot(c[1], c[2])] for c in curve]
        floor = abs(autocorrelation(sv, math.pi, 1200)[0])
        wrap_items.append([{'type': 'curve', 'points': ring, 'color': '#444', 'name': '|S| = 0 (orthogonal)'},
                           {'type': 'curve', 'points': mods, 'color': '#1B6F8C', 'name': '|S(θ)|, p_n ∝ n^-%g' % sv},
                           {'type': 'curve', 'points': two_mod, 'color': '#B5530F', 'dash': True,
                            'name': 'two-level state: touches 0 at θ = π'},
                           {'type': 'points', 'points': [[-1, 0, floor]], 'color': '#B5530F', 'marker': 'star',
                            'size': 11, 'name': 'the floor |S(π)| = %.4f' % floor}])
    smin = min(math.hypot(*autocorrelation(s, x)) for x in ts)
    return json.dumps({
        'text': ('Populations p_n ∝ n^-%g on the levels n = 1, 2, …: min |S| on the grid = %.6f, at θ = π, where '
                 '|S(π)| = η(s)/ζ(s). For s = 2 this is (π²/12)/(π²/6) = 1/2: the paper certifies it numerically, '
                 'and since 21-oct-2026 it is in Lean for every θ (Dilog.zetaState_norm_ge_half). The two-level state (orange) reaches 0 at θ = π: that clock ticks. Above: the curve '
                 '(θ, Re S, Im S) never meets the black line S = 0; below: |S| wrapped on the circle, lowest at '
                 'the antipode (star). Slide s. Series truncated at '
                 'n ≤ %d.' % (s, smin, NMAX)),
        'plots': [{'kind': '3d', 'title': 'S(θ) = Σ p_n e^{−inθ} as (θ, Re S, Im S): it never reaches the axis',
                   'axes': ['θ', 'Re S', 'Im S'], 'items': [],
                   'slider': {'label': 's (p_n ∝ n^-s)', 'values': svals, 'items': slider_items},
                   'figure': 'paperfig-3', 'panel': 'a', 'max_width': 1000},
                  {'kind': '3d', 'title': '|S(θ)| wrapped on the unit circle: the floor sits at the antipode θ = π',
                   'axes': ['cos θ', 'sin θ', '|S|'], 'items': [],
                   'slider': {'label': 's (p_n ∝ n^-s)', 'values': svals, 'items': wrap_items,
                              'start': svals.index(s)},
                   'figure': 'paperfig-3', 'panel': 'b', 'max_width': 1000}]})
