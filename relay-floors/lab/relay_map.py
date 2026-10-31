# encaje: segundo laboratorio del blueprint relay-floors: mapa de diseño con dos fronteras (V207 §7): para un error
# objetivo, sobre (g, T2* del cúbit peor), imposible por la cota / alcanzable por un pulso testigo / sin resolver.
# Python puro (Pyodide); usa relay_floor (suelo) y relay_lindblad (pulsos testigo).
"""run_map: what does a link need to reach a target error?

For a target ε on 1 - F_B and a grid of couplings g and of the T2* of the worse qubit (the other times fixed), each cell
is: EXCLUDED when the floor exceeds ε (no pulse can reach the target), REACHED when a witness pulse (minimal-time or
two sequential swaps, Lindblad) gets below ε (a construction exists within the model), and UNRESOLVED otherwise (the
bound allows it, our simple pulses do not reach it). The bound gives necessity, the witness sufficiency."""
import json
import math

import labkit as K
import relay_floor as RF
import relay_lindblad as RL

E4 = 1e4
COL = {'excluded': '#E57373', 'reached': '#81C784', 'unresolved': '#FFD54F'}


def _witness(qa, bus, qb, g_mhz):
    G = 2 * math.pi * g_mhz
    e1 = RL.minimal_time_error(qa, bus, qb, g_mhz, steps=100)[0]       # G·T ≈ 2.2 rad: 100 RK4 steps, error ~1e-8
    gseq, Tseq = RL.pulse_sequential(G)
    e2, _ = RL.evolve(gseq, Tseq, qa, bus, qb, steps=140, samples=2)
    return min(e1, e2)


def _heat(cells, xs, ys, here, title, xlabel, ylabel):
    """cells[i][j] for x = xs[i], y = ys[j]: a categorical heat map with the reader's link marked."""
    W, H, L, B, T, R = 560, 360, 64, 46, 14, 14
    nx, ny = len(xs), len(ys)
    cw, ch = (W - L - R) / nx, (H - T - B) / ny
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (W, H + 60)]
    for i in range(nx):
        for j in range(ny):
            st, fl, wt = cells[i][j]
            o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" stroke="#fff" stroke-width="1">'
                     '<title>g/2π = %.3g MHz, T2* = %.3g µs: %s (floor %.3g, witness %.3g × 10⁻⁴)</title></rect>'
                     % (L + i * cw, T + (ny - 1 - j) * ch, cw, ch, COL[st], xs[i], ys[j], st, fl * E4, wt * E4))
    for i in range(0, nx, max(1, nx // 5)):
        o.append('<text x="%.1f" y="%d" font-size="10" text-anchor="middle">%s</text>'
                 % (L + (i + 0.5) * cw, H - B + 14, K._tick(xs[i])))
    for j in range(0, ny, max(1, ny // 5)):
        o.append('<text x="%d" y="%.1f" font-size="10" text-anchor="end">%s</text>'
                 % (L - 4, T + (ny - 1 - j + 0.5) * ch + 3, K._tick(ys[j])))
    hx = L + (math.log(here[0] / xs[0]) / math.log(xs[-1] / xs[0]) * (nx - 1) + 0.5) * cw
    hy = T + (ny - 1 - math.log(here[1] / ys[0]) / math.log(ys[-1] / ys[0]) * (ny - 1) + 0.5) * ch
    o.append('<circle cx="%.1f" cy="%.1f" r="7" fill="none" stroke="#111" stroke-width="2.5"/>' % (hx, hy))
    o.append('<text x="%.1f" y="%.1f" font-size="11" font-weight="bold">your link</text>' % (hx + 10, hy - 8))
    o.append('<text x="%d" y="%d" font-size="12" text-anchor="middle">%s</text>' % ((L + W - R) / 2, H - 10, K.esc(xlabel)))
    o.append('<text x="14" y="%d" font-size="12" text-anchor="middle" transform="rotate(-90 14 %d)">%s</text>'
             % (H / 2, H / 2, K.esc(ylabel)))
    for k, (name, lab) in enumerate((('excluded', 'impossible: the floor is above the target'),
                                     ('reached', 'reached: a simple pulse is below the target'),
                                     ('unresolved', 'unresolved: allowed by the bound, not reached by our pulses'))):
        y0 = H + 8 + 16 * k                       # one legend line per region (no overlap)
        o.append('<rect x="%d" y="%d" width="12" height="10" fill="%s"/><text x="%d" y="%d" font-size="11">%s</text>'
                 % (L, y0, COL[name], L + 16, y0 + 9, K.esc(lab)))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': title}


def random_map():
    """The dice: a plausible link and a target between 1 and 50 × 10⁻⁴ (every input changes)."""
    import random
    import relay_lab
    p = json.loads(relay_lab.random_link())
    return json.dumps({'g_mhz': p['ga_mhz'], 't1a': p['t1a'], 't2a': p['t2a'], 't1c': p['t1c'], 't2c': p['t2c'],
                       't1b': p['t1b'], 't2b': p['t2b'], 'target': '%.1f' % random.uniform(1, 50),
                       'n': str(random.randint(5, 8))})


def run_map(params):
    p = json.loads(params) if isinstance(params, str) else params
    try:
        val = lambda k, d: float(str(p.get(k, d)).strip() or d)
        g0 = val('g_mhz', 9)
        qa, bus, qb = (val('t1a', 99.7), val('t2a', 7.1)), (val('t1c', 38.6), val('t2c', 51.0)), (val('t1b', 112.6), val('t2b', 60.0))
        eps = val('target', 10) / E4
        n = int(val('n', 7))
    except (TypeError, ValueError):
        return K.error('every field is a number')
    if not (0.05 <= g0 <= 500 and 0 < eps < 0.5 and 4 <= n <= 14):
        return K.error('g/2π 0.05–500 MHz; target between 0 and 5000 × 10⁻⁴; grid 4–14')
    for e in (qa, bus, qb):
        if not (0.01 <= e[0] <= 1e6 and 0.01 <= e[1] <= 2 * e[0] * (1 + 1e-9)):
            return K.error('times between 0.01 and 10⁶ µs, with T2 ≤ 2 T1')
    worse = 'A' if qa[1] <= qb[1] else 'B'
    w = qa if worse == 'A' else qb
    xs = [g0 * 0.5 * 6 ** (k / (n - 1)) for k in range(n)]                       # 0.5 g0 … 3 g0
    top = min(2 * w[0], 8 * w[1])
    ys = [w[1] * 0.5 * (top / (0.5 * w[1])) ** (k / (n - 1)) for k in range(n)]  # 0.5 T2* … min(2 T1, 8 T2*)
    cells = []
    for g in xs:
        col = []
        for t2 in ys:
            a, b = ((w[0], t2), qb) if worse == 'A' else (qa, (w[0], t2))
            fl = RF.floor(a, bus, b, g, grid=28)[0]
            if fl > eps:
                col.append(('excluded', fl, float('nan')))
                continue
            wt = _witness(a, bus, b, g)
            col.append(('reached' if wt < eps else 'unresolved', fl, wt))
        cells.append(col)
    here = (g0, w[1])
    fig = _heat(cells, xs, ys, here, '⑥ What you need for 1 − F_B < %s × 10⁻⁴' % K._tick(eps * E4),
                'coupling g/2π (MHz)', 'T2* of the worse qubit %s (µs)' % ('A' if worse == 'A' else 'B'))
    j0 = min(range(n), key=lambda j: abs(math.log(ys[j] / w[1])))               # the row of your T2*
    row = [cells[i][j0][0] for i in range(n)]
    g_need = next((xs[i] for i in range(n) if row[i] != 'excluded'), None)
    g_reach = next((xs[i] for i in range(n) if row[i] == 'reached'), None)
    txt = ('DESIGN MAP. Target 1 − F_B < %s × 10⁻⁴, varying the coupling and the T2* of the worse qubit (%s), the other '
           'coherence times fixed as given. Red: the floor is above the target, so no pulse can reach it (necessity, '
           'rigorous). Green: a simple pulse (minimal-time or two sequential swaps, Lindblad) is below it, so the target '
           'is reachable within the model (sufficiency). Amber: the bound allows it but our simple pulses do not reach '
           'it; a better pulse may, or may not. ' % (K._tick(eps * E4), 'qubit ' + worse))
    txt += ('At your T2*: the bound excludes the target below %s; a simple pulse reaches it from %s. '
            % ('g/2π ≈ %s MHz' % K._tick(g_need) if g_need else 'every coupling in the map',
               'g/2π ≈ %s MHz' % K._tick(g_reach) if g_reach else 'no coupling in the map'))
    txt += ('These are statements within the model (one effective bus mode, Markovian dephasing, coherence times that '
            'do not change with the coupling), not promises about a device.')
    return K.result(txt, [fig])
