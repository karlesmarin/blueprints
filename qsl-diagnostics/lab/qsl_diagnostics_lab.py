# encaje: laboratorios del blueprint qsl-diagnostics (Python puro; corre en el navegador con Pyodide y en local).
"""Labs of «Certified Speed-Limit Diagnostics for Deployed Superconducting Quantum Processors»: the computed figures
of the paper, live.

- run_fig1: Figure 1, the minimum X-gate time with optimal control (a surface over the anharmonicity and the drive
  fraction) with the IBM processors above it; a slider moves a marker along the surface and prints the gate time in ns.
- run_fig2: Figure 2, the first-order cross-resonance CNOT time t = (pi/2)/nu_ZX over (Omega_CR/Delta, Delta), the
  exchange-limit plane pi/(2J), the IBM processors; one slider for the coupling J and one for the anharmonicity.
- run_fig4: Figure 4, the law T_min ~ max(pi/Omega_max, ~1.1*2pi/|delta|) in ns for a chosen |delta|.

Numbers: Table V of the paper (grape_1q.py): r = 0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.5 give T|delta| = 32.99, 16.49,
12.04, 8.17, 7.07, 6.91, 7.33 (RESULTADOS.md, «Cuánto puede subir la fracción de un cúbit»); between them, log-log
interpolation (as paper/figuras_3d.py). The IBM points are per-backend medians (qsl_data.py, from qiskit-terra 0.24.1).
Test locally with prueba_labs.py."""
import json
import math

import labkit as K
from qsl_data import CHIPS, J_MEDIAN

R_TAB = [0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.5]
T_TAB = [32.99, 16.49, 12.04, 8.17, 7.07, 6.91, 7.33]   # T_min * |delta| (dimensionless), Table V
DOS_PI = 2 * math.pi
FALCON_X_NS = 35.6          # Falcon single-qubit gate duration quoted in the paper (jakarta)
LEAK = 1.1 * DOS_PI         # the leakage floor of Eq. (1): ~1.1 periods of 2*pi/|delta|, as T*|delta|


def t_delta(r):
    """T_min*|delta| at drive fraction r: log-log interpolation inside the measured grid [0.1, 1.5]; below 0.1 the
    speed-limit branch is continued (T*|delta| proportional to 1/r, the 1.05*pi/Omega branch): NOT computed."""
    if r > R_TAB[-1] or r <= 0:
        raise ValueError('outside the measured grid')
    if r < R_TAB[0]:
        return T_TAB[0] * R_TAB[0] / r
    for i in range(len(R_TAB) - 1):
        if R_TAB[i] <= r <= R_TAB[i + 1]:
            a = (math.log(r) - math.log(R_TAB[i])) / (math.log(R_TAB[i + 1]) - math.log(R_TAB[i]))
            return math.exp(math.log(T_TAB[i]) + a * (math.log(T_TAB[i + 1]) - math.log(T_TAB[i])))


def rad_ns(mhz):
    """|delta|/2pi in MHz -> |delta| in rad/ns."""
    return DOS_PI * mhz / 1000.0


def t_x_ns(r, mhz):
    return t_delta(r) / rad_ns(mhz)


def t_cr_ns(r, delta_cr_mhz, j, delta_mhz):
    """First-order cross-resonance CNOT time (pi/2)/nu_ZX, nu_ZX = J r |dc/(dc + Delta)|; dc = -|delta|, Delta > 0."""
    dc, big = -rad_ns(delta_mhz), rad_ns(delta_cr_mhz)
    if dc + big == 0:
        raise ValueError('Delta = |delta|: the first-order formula diverges')
    return (math.pi / 2) / (j * r * abs(dc / (dc + big)))


def _num(p, key, default, lo, hi, what):
    try:
        v = float(p.get(key, default))
    except (TypeError, ValueError):
        raise ValueError('%s is not a number' % what)
    if not lo <= v <= hi:
        raise ValueError('%s = %g is outside [%g, %g]' % (what, v, lo, hi))
    return v


def _scale(items, box, size=(10.0, 10.0, 7.0)):
    """Map every [x, y, z] of the items into a box of comparable sides: the turnable view draws all three axes at one
    scale, so a raw range of 0.85 against 1500 would show an edge-on sliver (seen in the browser, 27-oct). The ranges
    are written in the axis names instead of tick labels."""
    def f(p):
        return [(p[i] - box[i][0]) / (box[i][1] - box[i][0]) * size[i] for i in range(3)]
    out = []
    for it in items:
        it = dict(it)
        if it['type'] == 'surface':
            it['grid'] = [[f(p) for p in row] for row in it['grid']]
        else:
            it['points'] = [f(p) for p in it['points']]
        out.append(it)
    return out


# ------------------------------------------------------------------ Figure 1 (single qubit)

def run_fig1(params):
    p = json.loads(params)
    try:
        mhz = _num(p, 'delta_mhz', 330, 200, 450, '|delta|/2pi (MHz)')
        r = _num(p, 'r', 0.1, 0.1, 1.5, 'the drive fraction r (the measured grid is 0.1 to 1.5)')
    except ValueError as e:
        return K.error(str(e))
    # |delta|/2pi, MHz: 280 .. 360 (the IBM processors), widened to hold the reader's |delta| (30-oct: a random
    # |delta| = 236 MHz put the marker outside the drawn box)
    x0, x1 = min(280, 20 * math.floor(mhz / 20)), max(360, 20 * math.ceil(mhz / 20))
    xs = [x0 + (x1 - x0) * i / 16 for i in range(17)]
    ys = [math.log10(0.06) + (math.log10(1.5) - math.log10(0.06)) * i / 30 for i in range(31)]   # log10 r
    meas = [y for y in ys if y >= math.log10(0.1) - 1e-9]
    extra = [y for y in ys if y <= math.log10(0.1) + 1e-9]
    z = lambda x, y: t_x_ns(10 ** y, x)
    fixed = [K.surface3(z, xs, meas, 'minimum X time, optimal control (measured grid r = 0.1 to 1.5)',
                        color='#1B6F8C', opacity=0.55),
             K.surface3(z, xs, extra, 'continued as 1/r below r = 0.1 (not computed)', color='#9AA7B0', opacity=0.4)]
    orange, rows, pts, feet = '#B5530F', [], [], []
    for k, (name, de, r1, tau, rcr, dl, tcx, jq) in enumerate(CHIPS):
        if tau > 200:                                           # toronto: 2560-sample X pulse, not shown (as the paper)
            continue
        dm, lr, zs = de / DOS_PI * 1000, math.log10(r1), t_delta(r1) / de if r1 <= 1.5 else float('nan')
        pts.append([dm, lr, tau])
        feet.append([dm, lr, zs])
        fixed.append(K.curve3([[dm, lr, zs], [dm, lr, tau]], 'gap: IBM time above the minimum at the same r' if not
                              [1 for c in fixed if c.get('name', '').startswith('gap')] else '',
                              color='#5C5B55', width=1.5))
        rows.append([name, '%.0f' % dm, '%.3f' % r1, '%.1f' % tau, '%.1f%s' % (zs, '*' if r1 < 0.1 else ''),
                     '%.2f' % (tau / zs)])
    fixed.append(K.points3(feet, 'minimum at the same r', color='#1B6F8C', size=3))
    fixed.append(K.points3(pts, 'IBM processors (median X duration)', color=orange, size=6))
    grid = sorted(set([0.1, 0.15, 0.2, 0.3, 0.4, 0.5, 0.65, 0.8, 1.0, 1.25, 1.5] + [round(r, 4)]))
    frames, labels = [], []
    for g in grid:
        t = t_x_ns(g, mhz)
        frames.append([K.points3([[mhz, math.log10(g), t]], 'marker: T_min at r = %.2f, |delta|/2pi = %g MHz' % (g, mhz),
                                 color='#C62828', size=11, star=True),
                       K.curve3([[x, math.log10(g), t_x_ns(g, x)] for x in xs], 'same r, other anharmonicities',
                                color='#C62828', width=2, dash=True),
                       K.curve3([[mhz, math.log10(g), 0], [mhz, math.log10(g), t]], '', color='#C62828', width=1)])
        labels.append('%.2f → %.1f ns' % (g, t))
    t = t_x_ns(r, mhz)
    ns_limit = math.pi / (r * rad_ns(mhz))
    text = ('At |&delta;|/2&pi; = %g MHz and drive fraction r = &Omega;<sub>max</sub>/|&delta;| = %g, optimal control on the '
            '4-level transmon gives T<sub>min</sub>|&delta;| = %.2f, that is <b>%.1f ns</b>; the two-level limit '
            '&pi;/&Omega;<sub>max</sub> is %.1f ns (ratio %.2f). Orange: IBM processors (per-backend medians of '
            '|&delta;|, &Omega;<sub>peak</sub>/|&delta;| and X duration, pulses of qiskit-terra 0.24.1); grey: the gap. '
            'Where r &lt; 0.1 (marked * in the table) the surface is the 1/r continuation of the measured branch, not '
            'a computation; the static figure of the paper holds T|&delta;| constant there.'
            % (mhz, r, t_delta(r), t, ns_limit, t / ns_limit))
    # the time ceiling follows what is drawn: at a low |delta| the 1/r continuation below r = 0.1 passes 40 ns and
    # was clipped (30-oct, random |delta| = 207 MHz)
    zs_all = [p[2] for it in fixed + [i for fr in frames for i in fr]
              for p in (sum(it['grid'], []) if it['type'] == 'surface' else it['points'])
              if isinstance(p[2], (int, float)) and math.isfinite(p[2])]
    ztop = max(40, 10 * math.ceil(max(zs_all) / 10))
    box = ((x0, x1), (math.log10(0.06), math.log10(1.5)), (0, ztop))
    fixed = _scale(fixed, box)
    frames = [_scale(fr, box) for fr in frames]
    plot = K.three_d(fixed, 'Figure 1 live: minimum X-gate time, with IBM processors above it',
                     axes=('|δ|/2π: %d to %d MHz' % (x0, x1), 'drive fraction Ω/|δ|: 0.06 to 1.5 (log)',
                           'X-gate time: 0 to %d ns' % ztop),
                     slider={'label': 'drive fraction r', 'values': labels, 'items': frames,
                             'start': grid.index(round(r, 4))})
    plot['figure'] = 'paperfig-1'
    return K.result(text, [plot], K.table(['backend', '|δ|/2π (MHz)', 'Ω_peak/|δ|', 'X duration (ns)',
                                           'minimum at same r (ns)', 'IBM / minimum'], rows))


# ------------------------------------------------------------------ Figure 2 (two qubits)

def _cr_frame(j, delta_mhz, rr, dd, chips):
    """Items of one state of Figure 2: the surface, the exchange-limit plane, the processors with their drops."""
    lim = math.pi / (2 * j)
    items = [K.surface3(lambda r, d: t_cr_ns(r, d, j, delta_mhz), rr, dd,
                        'first-order cross resonance, t = (π/2)/ν_ZX', color='#1B6F8C', opacity=0.55),
             K.surface3(lambda r, d: lim, [rr[0], rr[-1]], [dd[0], dd[-1]],
                        'exchange limit π/(2J) = %.0f ns' % lim, color='#EB6834', opacity=0.3)]
    pts = []
    for k, (r, dl, t) in enumerate(chips):
        s = t_cr_ns(r, dl, j, delta_mhz)
        items.append(K.curve3([[r, dl, lim], [r, dl, s]], 'dilution by the cross-resonance mechanism (plane to surface)'
                              if k == 0 else '', color='#1B6F8C', width=1.2, dash=True))
        items.append(K.curve3([[r, dl, s], [r, dl, t]], 'echo pulses and ramps (surface to point)' if k == 0 else '',
                              color='#5C5B55', width=1.5))
        pts.append([r, dl, t])
    items.append(K.points3(pts, 'IBM processors (median CX)', color='#B5530F', size=6))
    return items


def run_fig2(params):
    p = json.loads(params)
    try:
        j = _num(p, 'j', J_MEDIAN, 0.002, 0.05, 'the coupling J (rad/ns)')
        mhz = _num(p, 'delta_mhz', 330, 150, 500, '|delta|/2pi (MHz)')
        r = _num(p, 'r', 0.45, 0.05, 1.5, 'the drive fraction r = Omega_CR/Delta')
        dmhz = _num(p, 'detuning_mhz', 115, 40, 160, 'the detuning |Delta|/2pi (MHz)')
        t = t_cr_ns(r, dmhz, j, mhz)
    except ValueError as e:
        return K.error(str(e))
    rr = [0.15 + 0.85 * i / 15 for i in range(16)]
    dd = [40 + 120 * i / 15 for i in range(16)]
    chips = []
    for (name, de, r1, tau, rcr, dl, tcx, jq) in CHIPS:
        dm = dl / DOS_PI * 1000
        if 0.15 <= rcr <= 1.0 and 40 <= dm <= 160:
            chips.append((rcr, dm, tcx))
    js = sorted(set([round(j * f, 6) for f in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0)]))
    ds = sorted(set([200, 250, 300, 330, 360, 400, 450, round(mhz, 3)]))
    fa = [_cr_frame(x, mhz, rr, dd, chips) for x in js]
    fb = [_cr_frame(j, x, rr, dd, chips) for x in ds]
    zmax = max(max(it['grid'][i][k][2] for it in fr if it['type'] == 'surface' for i in range(len(it['grid']))
                   for k in range(len(it['grid'][0]))) for fr in fa + fb)
    zmax = 100 * math.ceil(zmax * 1.02 / 100)
    box = ((0.15, 1.0), (40, 160), (0, zmax))
    fa = [_scale(fr, box) for fr in fa]
    fb = [_scale(fr, box) for fr in fb]
    ax = ('Ω_CR/Δ: 0.15 to 1', '|Δ|/2π: 40 to 160 MHz', 'CNOT time: 0 to %d ns' % zmax)
    pa = K.three_d([],'Figure 2 live, slider on the coupling J: the exchange limit π/(2J) and the surface both move',
                   axes=ax, slider={'label': 'J (rad/ns)', 'values': ['%.4f → limit %.0f ns' % (x, math.pi / (2 * x))
                                                                          for x in js],
                                    'items': fa, 'start': js.index(round(j, 6))})
    pa['figure'] = 'paperfig-2'
    pb = K.three_d([], 'Same figure, slider on the anharmonicity |δ|/2π at the chosen J',
                   axes=ax, slider={'label': '|δ|/2π (MHz)', 'values': ['%g' % x for x in ds], 'items': fb,
                                    'start': ds.index(round(mhz, 3))})
    lim = math.pi / (2 * j)
    text = ('With J = %.4f rad/ns the exchange limit &pi;/(2J) is <b>%.1f ns</b>. At r = &Omega;<sub>CR</sub>/&Delta; = '
            '%g, |&Delta;|/2&pi; = %g MHz and |&delta;|/2&pi; = %g MHz, the first-order cross-resonance CNOT lasts '
            '(&pi;/2)/&nu;<sub>ZX</sub> = <b>%.1f ns</b>, %.2f times the limit. The orange points are the median '
            'CX duration of %d IBM processors with calibrated cross-resonance pulses (qiskit-terra 0.24.1); the '
            'formula is first order (no ZZ, IX or classical crosstalk), as the paper states.'
            % (j, lim, r, dmhz, mhz, t, t / lim, len(chips)))
    rows = [[n, '%.3f' % rcr, '%.0f' % (dl / DOS_PI * 1000), '%.0f' % tcx, '%.0f' % t_cr_ns(rcr, dl / DOS_PI * 1000, j, mhz)]
            for (n, de, r1, tau, rcr, dl, tcx, jq) in CHIPS if 0.15 <= rcr <= 1.0 and 40 <= dl / DOS_PI * 1000 <= 160]
    return K.result(text, [pa, pb], K.table(['backend', 'Ω_CR/Δ', '|Δ|/2π (MHz)', 'IBM CX (ns)',
                                             'first-order t (ns)'], rows))


# ------------------------------------------------------------------ Figure 4 (the law)

def run_fig4(params):
    p = json.loads(params)
    try:
        mhz = _num(p, 'delta_mhz', 330, 100, 600, '|delta|/2pi (MHz)')
        r = _num(p, 'r', 0.1, 0.1, 1.5, 'the drive fraction r (the measured grid is 0.1 to 1.5)')
    except ValueError as e:
        return K.error(str(e))
    d = rad_ns(mhz)
    # the legend goes below the plot, in two columns, never over the data (30-oct: with random values the curves
    # crossed the old lower-left legend); lines are clipped to the frame (the two-level line left it at the bottom)
    W, H, L, R, T, B, LEG = 600, 390, 62, 18, 30, 98, 50
    x0, x1 = math.log10(0.08), math.log10(2.0)
    law = lambda rr: max(math.pi / rr, LEAK) / d
    ymin = math.log10(min(T_TAB) / d * 0.6)
    ymax = math.log10(max(law(0.08), FALCON_X_NS) * 1.3)
    X = lambda v: L + (math.log10(v) - x0) / (x1 - x0) * (W - L - R)
    Y = lambda v: H - B - (math.log10(v) - ymin) / (ymax - ymin) * (H - T - B)
    # explicit width and height: the slot that replaces the paper's figure is a flex item and collapses to 0 px
    # around an svg that only has a viewBox (seen in the browser, 27-oct)
    o = ['<svg viewBox="0 0 %d %d" width="%d" height="%d" style="max-width:100%%;background:#fff" '
         'xmlns="http://www.w3.org/2000/svg">' % (W, H, W, H),
         '<defs><clipPath id="lm-f4-frame"><rect x="%d" y="%d" width="%d" height="%d"/></clipPath></defs>'
         % (L, T, W - L - R, H - T - B),
         '<rect x="%d" y="%d" width="%d" height="%d" fill="none" stroke="#ccc"/>' % (L, T, W - L - R, H - T - B)]
    for v in (0.1, 0.2, 0.5, 1.0, 2.0):
        o.append('<line x1="%.1f" x2="%.1f" y1="%d" y2="%d" stroke="#eee"/><text x="%.1f" y="%d" font-size="10" '
                 'text-anchor="middle">%g</text>' % (X(v), X(v), T, H - B, X(v), H - B + 14, v))
    tick = 1
    while tick < 10 ** ymax:
        for m in (1, 2, 5):
            v = tick * m
            if 10 ** ymin <= v <= 10 ** ymax:
                o.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#eee"/><text x="%d" y="%.1f" font-size="10" '
                         'text-anchor="end">%g</text>' % (L, W - R, Y(v), Y(v), L - 4, Y(v) + 3, v))
        tick *= 10
    rs = [0.08 * (2.0 / 0.08) ** (i / 80) for i in range(81)]
    o.append('<g clip-path="url(#lm-f4-frame)">')   # only the data is clipped, not the ticks and their labels
    o.append('<path d="M%s" fill="none" stroke="#9AA7B0" stroke-width="1.5" stroke-dasharray="5 4"/>'
             % ' L'.join('%.1f %.1f' % (X(q), Y(math.pi / q / d)) for q in rs))
    o.append('<path d="M%s" fill="none" stroke="#2E7D32" stroke-width="2.5"/>'
             % ' L'.join('%.1f %.1f' % (X(q), Y(law(q))) for q in rs))
    o.append('<line x1="%.1f" x2="%.1f" y1="%d" y2="%d" stroke="#B5530F" stroke-width="2"/>' % (X(0.1), X(0.1), T, H - B))
    o.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#C62828" stroke-dasharray="2 3"/>'
             % (L, W - R, Y(FALCON_X_NS), Y(FALCON_X_NS)))
    for rt, tt in zip(R_TAB, T_TAB):
        o.append('<circle cx="%.1f" cy="%.1f" r="4.5" fill="#1B6F8C"/>' % (X(rt), Y(tt / d)))
    o.append('<circle cx="%.1f" cy="%.1f" r="7" fill="none" stroke="#000" stroke-width="2"/>' % (X(r), Y(t_x_ns(r, mhz))))
    o.append('</g>')
    leg = [('#1B6F8C', 'optimal control, Table V (4 levels)'), ('#2E7D32', 'law max(π/Ω, 1.1·2π/|δ|)'),
           ('#9AA7B0', 'two-level limit π/Ω'), ('#B5530F', 'IBM cap r ≈ 0.1'), ('#C62828', 'IBM Falcon X, 35.6 ns')]
    for k, (c, n) in enumerate(leg):
        lx, ly = L + 10 + (k % 2) * 260, H - LEG + 8 + 14 * (k // 2)
        o.append('<rect x="%d" y="%d" width="12" height="4" fill="%s"/><text x="%d" y="%d" font-size="11">%s</text>'
                 % (lx, ly - 4, c, lx + 18, ly + 1, n))
    o.append('<text x="%d" y="%d" text-anchor="middle" font-size="12">drive bound r = Ω_max/|δ|</text>'
             % (W / 2, H - B + 32))
    o.append('<text x="14" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 14 %d)">minimum X time (ns), '
             '|δ|/2π = %g MHz</text>' % (H / 2, H / 2, mhz))
    o.append('</svg>')
    tab = t_x_ns(r, mhz)
    lw = law(r)
    text = ('At |&delta;|/2&pi; = %g MHz (|&delta;| = %.3f rad/ns): optimal control at r = %g gives T<sub>min</sub>|&delta;| '
            '= %.2f, <b>%.1f ns</b>; the law max(&pi;/&Omega;<sub>max</sub>, 1.1&middot;2&pi;/|&delta;|) gives %.1f ns '
            '(%+.0f%% against the table: the paper calls it an empirical fit to a coarse grid, not a theorem). At IBM\'s cap '
            'r = 0.1 the optimum is %.1f ns; at the leakage floor 1.1&middot;2&pi;/|&delta;| = <b>%.1f ns</b>. The two '
            'branches cross at r = &pi;/(1.1&middot;2&pi;) = %.3f. The circle marks your r; the blue dots are the '
            'table\'s points.'
            % (mhz, d, r, t_delta(r), tab, lw, 100 * (lw / tab - 1), t_x_ns(0.1, mhz), LEAK / d, 1 / (2 * 1.1)))
    return K.result(text, [{'kind': 'svg', 'svg': ''.join(o), 'figure': 'paperfig-4'}],
                    K.table(['r', 'T_min|δ| (Table V)', 'T_min at this |δ| (ns)', 'law (ns)'],
                            [['%g' % a, '%.2f' % b, '%.1f' % (b / d), '%.1f' % law(a)] for a, b in zip(R_TAB, T_TAB)]))
