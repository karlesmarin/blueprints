# encaje: laboratorio de la Figura 3 del blueprint qsl-diagnostics (serie temporal 2021-2025; Python puro, Pyodide).
"""run_fig3: Figure 3 live. The per-year statistic of the per-snapshot medians (serie.csv, 56 usable snapshots), for
one or both gaps, optionally split by the dominant two-qubit gate (CX/ECR) or by the qubit count of the processor,
with backends left out on request. The summary adds the within-backend comparison (the same processor at its first
and last date), because a trend between dates read on pooled snapshots can be confounding by fleet change: the
paper's own lesson (Section VI). Data: SERIE in qsl_data.py (gen_datos.py)."""
import json
import math
import statistics as st

import labkit as K
import qsl_diagnostics_lab as S
from qsl_data import SERIE

QUANT = {'1q': ('single-qubit X, τ_X/τ_QSL', 4, '#1B6F8C'), '2q': ('two-qubit CX/ECR, τ_2q/(π/2j_q)', 5, '#B5530F')}
DASH = ['', '6 3', '2 3', '8 3 2 3', '1 2']
STATS = {'median': st.median, 'mean': st.mean}


def _group(row, by):
    if by == 'gate':
        return row[3].upper() or 'no 2q gate'
    if by == 'qubits':
        return '%d qubits' % row[2]
    return 'all'


def _svg(lines, years, ymax, dots):
    """lines: [(label, colour, dash, {year: value})]; dots: [(year, value, colour)] one per snapshot."""
    W, H, L, R, T, B = 600, 330, 52, 16, 20, 40
    X = lambda i: L + (i + 0.5) / len(years) * (W - L - R)
    Y = lambda v: H - B - v / ymax * (H - T - B)
    o = ['<svg viewBox="0 0 %d %d" width="%d" height="%d" style="max-width:100%%;background:#fff" '
         'xmlns="http://www.w3.org/2000/svg">' % (W, H, W, H)]
    step = 2 if ymax <= 16 else 5 if ymax <= 40 else 10
    v = 0
    while v <= ymax + 1e-9:
        o.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#eee"/><text x="%d" y="%.1f" font-size="10" '
                 'text-anchor="end">%g</text>' % (L, W - R, Y(v), Y(v), L - 4, Y(v) + 3, v))
        v += step
    for i, y in enumerate(years):
        o.append('<text x="%.1f" y="%d" font-size="11" text-anchor="middle">%s</text>' % (X(i), H - B + 15, y))
    for k, (y, v, c) in enumerate(dots):     # the snapshots, spread inside their year so that they do not overlap
        if v <= ymax:
            o.append('<circle cx="%.1f" cy="%.1f" r="2.2" fill="%s" fill-opacity="0.35"/>'
                     % (X(years.index(y)) + ((k * 7) % 23 - 11), Y(v), c))
    for n, (label, c, dash, vals) in enumerate(lines):
        pts = [(X(i), Y(vals[y])) for i, y in enumerate(years) if y in vals]
        if len(pts) > 1:
            o.append('<path d="M%s" fill="none" stroke="%s" stroke-width="2.2"%s/>'
                     % (' L'.join('%.1f %.1f' % p for p in pts), c, ' stroke-dasharray="%s"' % dash if dash else ''))
        for (x, yy) in pts:
            o.append('<circle cx="%.1f" cy="%.1f" r="4" fill="%s"/>' % (x, yy, c))
        o.append('<line x1="%d" x2="%d" y1="%d" y2="%d" stroke="%s" stroke-width="2.2"%s/><text x="%d" y="%d" '
                 'font-size="11">%s</text>' % (L + 8, L + 26, T + 8 + 14 * n, T + 8 + 14 * n, c,
                                               ' stroke-dasharray="%s"' % dash if dash else '', L + 30,
                                               T + 12 + 14 * n, K.esc(label)))
    o.append('<text x="14" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 14 %d)">gate time / speed '
             'limit</text>' % (H / 2, H / 2))
    o.append('</svg>')
    return ''.join(o)


def _within(rows, col):
    """Backends seen in two different years: (backend, first year, last year, first value, last value)."""
    by = {}
    for r in rows:
        if r[col] is not None:
            by.setdefault(r[0], []).append((r[1], r[col]))
    out = []
    for b, v in by.items():
        v.sort()
        if v[0][0][:4] != v[-1][0][:4]:
            out.append((b, v[0][0][:4], v[-1][0][:4], v[0][1], v[-1][1]))
    return sorted(out)


def run_fig3(params):
    p = json.loads(params)
    q = str(p.get('quantity', 'both')).strip().lower()
    by = str(p.get('split', 'none')).strip().lower()
    stat = str(p.get('statistic', 'median')).strip().lower()
    if q not in ('both', '1q', '2q'):
        return K.error('quantity is both, 1q or 2q')
    if by not in ('none', 'gate', 'qubits'):
        return K.error('split is none, gate or qubits')
    if stat not in STATS:
        return K.error('statistic is median or mean')
    try:
        y0, y1 = int(p.get('from', 2021)), int(p.get('to', 2025))
    except (TypeError, ValueError):
        return K.error('the years are integers')
    if not 2021 <= y0 <= y1 <= 2025:
        return K.error('the years must satisfy 2021 ≤ from ≤ to ≤ 2025')
    drop = {b.strip().lower().replace('ibm_', '') for b in str(p.get('exclude', '')).split(',') if b.strip()}
    known = {r[0] for r in SERIE}
    if drop - known:
        return K.error('not in the series: %s (backends: %s)' % (', '.join(sorted(drop - known)), ', '.join(sorted(known))))
    rows = [r for r in SERIE if y0 <= int(r[1][:4]) <= y1 and r[0] not in drop]
    if not rows:
        return K.error('no snapshot left')
    years = [str(y) for y in range(y0, y1 + 1)]
    f = STATS[stat]
    lines, dots, tab, ymax = [], [], [], 0.0
    groups = sorted({_group(r, by) for r in rows}, key=lambda g: (len(g), g))
    for key in (['1q', '2q'] if q == 'both' else [q]):
        name, col, colour = QUANT[key]
        for gi, g in enumerate(groups):
            vals = {}
            for y in years:
                v = [r[col] for r in rows if r[1][:4] == y and _group(r, by) == g and r[col] is not None]
                if v:
                    vals[y] = f(v)
                    tab.append([name.split(',')[0], g, y, len(v), '%.2f' % vals[y]])
                    dots += [(y, x, colour) for x in v]
            if vals:
                lines.append((name if g == 'all' else '%s · %s' % (name.split(',')[0], g), colour,
                              DASH[gi % len(DASH)], vals))
                ymax = max(ymax, max(vals.values()))
    ymax = max(13.0, 2 * math.ceil(ymax * 1.15 / 2)) if ymax < 40 else 10 * math.ceil(ymax * 1.1 / 10)
    svg = _svg(lines, years, ymax, dots)
    # the summary: the pooled change, then the same processors at their first and last date
    parts = []
    for key in (['1q', '2q'] if q == 'both' else [q]):
        name, col, _ = QUANT[key]
        allv = [l for l in lines if l[0].startswith(name.split(',')[0])]
        for label, _, _, vals in allv:
            ys = sorted(vals)
            if len(ys) > 1:
                parts.append('%s: %.2f (%s) → %.2f (%s), %s %.0f%%' % (K.esc(label), vals[ys[0]], ys[0], vals[ys[-1]],
                             ys[-1], 'up' if vals[ys[-1]] > vals[ys[0]] else 'down',
                             abs(100 * (vals[ys[-1]] / vals[ys[0]] - 1))))
        w = _within(rows, col)
        if w:
            ch = [b[4] / b[3] for b in w]
            parts.append('same processor at its first and last year (%s, %d backends): median change ×%.2f, up in %d '
                         'of %d' % (name.split(',')[0], len(w), st.median(ch), sum(c > 1 for c in ch), len(ch)))
    per_year = ', '.join('%s: %d' % (y, sum(r[1][:4] == y for r in rows)) for y in years)
    thin = [y for y in years if 0 < sum(r[1][:4] == y for r in rows) < 5]
    text = ('Per-year %s of the snapshot medians, %d snapshots (%s)%s. %s. ' % (
                stat, len(rows), per_year, ', without ' + ', '.join(sorted(drop)) if drop else '',
                '; '.join(parts)) +
            ('Years resting on fewer than 5 snapshots: %s; read them with care. ' % ', '.join(thin) if thin else '') +
            'The pooled curve mixes a change of fleet (Falcon CX → Eagle ECR) with any change of the gates themselves; '
            'split by gate or by qubit count to separate them. The paper reports the pooled median (the default).')
    plots = [{'kind': 'svg', 'svg': svg, 'figure': 'paperfig-3', 'panel': 'a'}]
    for n, key in enumerate(['1q', '2q'] if q == 'both' else [q]):
        plots.append(_fleet3d(rows, key, stat, years))
        plots[-1].update({'figure': 'paperfig-3', 'panel': 'b%d' % n})
    return K.result(text, plots, K.table(['gap', 'group', 'year', 'snapshots', stat], tab))


GATE_COL = {'cx': '#1B6F8C', 'ecr': '#B5530F', '': '#9AA7B0'}


def _fleet3d(rows, key, stat, years):
    """The fleet in 3D: date × processor (ordered by qubit count) × ratio. Each processor is a thread through its
    snapshots (colour: its two-qubit gate); the per-year statistic of all of them runs along the front wall. The slider
    adds one year at a time: the pooled curve moves when the fleet changes even where no thread moves."""
    name, col, _ = QUANT[key]
    pts = [r for r in rows if r[col] is not None]
    order = sorted({r[0] for r in pts}, key=lambda b: (min(r[2] for r in pts if r[0] == b), b))
    idx = {b: i for i, b in enumerate(order)}
    vals = sorted(r[col] for r in pts)
    cap = 2 * math.ceil(vals[int(0.97 * (len(vals) - 1))] * 1.15 / 2)   # one outlier (toronto, ~40) would flatten all
    t = lambda d: int(d[:4]) + (int(d[5:7]) - 1) / 12 + (int(d[8:10]) - 1) / 365
    zc = lambda v: min(v, cap)
    frames, labels = [], []
    f = STATS[stat]
    pooled, named = {}, set()

    def nm(s):                    # a name only once over the slider (the legend lists every named item it shows)
        if s in named:
            return ''
        named.add(s)
        return s
    for y in years:
        fr = []
        yr = [r for r in pts if r[1][:4] == y]
        for g in ('cx', 'ecr', ''):
            sel = [r for r in yr if r[3] == g]
            if sel:
                fr.append(K.points3([[t(r[1]), idx[r[0]], zc(r[col])] for r in sel],
                                    nm('%s snapshots' % (g.upper() or 'no-gate')), color=GATE_COL[g], size=5))
        over = [r for r in yr if r[col] > cap]
        if over:
            fr.append(K.points3([[t(r[1]), idx[r[0]], cap] for r in over], nm('clipped at %g (true value above)' % cap),
                                color='#C62828', size=9, star=True))
        for b in {r[0] for r in yr}:          # the thread of each processor: the segments that end in this year
            mine = sorted((r for r in pts if r[0] == b), key=lambda r: r[1])
            for a, c in zip(mine, mine[1:]):
                if c[1][:4] == y:
                    fr.append(K.curve3([[t(a[1]), idx[b], zc(a[col])], [t(c[1]), idx[b], zc(c[col])]], '',
                                       color=GATE_COL[c[3]], width=1.6))
        if yr:
            pooled[y] = f([r[col] for r in yr])
            py = sorted(pooled)
            pc = K.curve3([[int(k) + 0.5, -2, zc(pooled[k])] for k in py],
                          'per-year %s of all snapshots (front wall)' % stat, color='#2E7D32', width=3.2)
            pc['current'] = True      # the curve so far is redrawn at each step, not stacked
            fr.append(pc)
            fr.append(K.points3([[int(y) + 0.5, -2, zc(pooled[y])]], '', color='#2E7D32', size=7))
        frames.append(fr)
        labels.append('up to %s (%d snapshots)' % (y, sum(len([r for r in pts if r[1][:4] == z]) for z in years
                                                           if z <= y)))
    box = ((int(years[0]), int(years[-1]) + 1), (-2, max(len(order) - 1, 1)), (0, cap))
    frames = [S._scale(fr, box) for fr in frames]
    floor = S._scale([K.surface3(lambda x, yy: 0, [box[0][0], box[0][1]], [box[1][0], box[1][1]], '', color='#e8edf1',
                                 opacity=0.25)], box)
    out = K.three_d(floor, 'The fleet in time, %s: one thread per processor (blue CX, orange ECR), the pooled %s on '
                    'the front wall' % (name, stat),
                    axes=('date: %s to %d' % (years[0], int(years[-1]) + 1),
                          'processor (by qubit count: %s … %s)' % (order[0], order[-1]),
                          'ratio: 0 to %g' % cap),
                    slider={'label': 'year', 'values': labels, 'items': frames, 'start': len(frames) - 1})
    out['slider']['cumulative'] = True
    return out
