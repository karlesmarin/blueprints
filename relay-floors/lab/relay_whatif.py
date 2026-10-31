# encaje: tercer laboratorio del blueprint relay-floors: «what if» en vivo (deslizadores); solo el suelo (0.05 s), para
# que responda al mover; Python puro (Pyodide); usa relay_floor.
"""run_whatif: move the coupling and the coherence times with sliders and watch the floor move.

Only bounds are computed here (no pulse simulation), so that the answer follows the slider. T2 above 2 T1 is clamped to
2 T1 (no pure dephasing) and said so."""
import json
import math

import labkit as K
import relay_floor as RF

E4 = 1e4


def run_whatif(params):
    p = json.loads(params) if isinstance(params, str) else params
    try:
        v = lambda k, d: float(str(p.get(k, d)).strip() or d)
        g = v('g_mhz', 9)
        t1a, t2a, t1c, t2c, t1b, t2b = (v('t1a', 99.7), v('t2a', 7.1), v('t1c', 38.6), v('t2c', 51.0),
                                        v('t1b', 112.6), v('t2b', 60.0))
    except (TypeError, ValueError):
        return K.error('every field is a number')
    if not (0.05 <= g <= 500 and min(t1a, t2a, t1c, t2c, t1b, t2b) >= 0.01):
        return K.error('g/2π 0.05–500 MHz; times ≥ 0.01 µs')
    notes = []
    fix = lambda name, t1, t2: (t1, t2) if t2 <= 2 * t1 else (notes.append(name) or (t1, 2 * t1))
    qa, bus, qb = fix('qubit A', t1a, t2a), fix('bus', t1c, t2c), fix('qubit B', t1b, t2b)
    fl, T = RF.floor(qa, bus, qb, g, grid=60)
    rel = lambda e: (e[0], 2 * e[0])
    rob, _ = RF.floor(rel(qa), rel(bus), rel(qb), g, grid=60)
    bound, _ = RF.link_bound(qa, bus, qb, g)
    ts = [T * 0.2 * (25 ** (k / 60)) for k in range(61)]
    plot = K.svg_plot([{'name': 'bound for every pulse of duration T (below: forbidden)', 'x': [1000 * t for t in ts],
                        'y': [bound(t) * E4 for t in ts], 'mode': 'area', 'color': '#7FA7C2'},
                       {'name': 'floor', 'x': [1000 * ts[0], 1000 * ts[-1]], 'y': [fl * E4] * 2, 'mode': 'line',
                        'color': '#6A1B9A'},
                       {'name': 'robust floor (any dephasing noise)', 'x': [1000 * ts[0], 1000 * ts[-1]],
                        'y': [rob * E4] * 2, 'mode': 'line', 'color': '#2E7D32'}],
                      title='The bound against the duration, as you move the sliders', xlabel='duration (ns, log scale)',
                      ylabel='1 − F_B (× 10⁻⁴, log scale)', logx=True, logy=True, height=280)
    share = 100 * (1 - rob / fl) if fl > 0 else 0
    card = ('<div style="display:flex;gap:.5em;flex-wrap:wrap;font:13px Arial,sans-serif">'
            + ''.join('<div style="flex:1;min-width:120px;background:#f6f9fb;border:1px solid #dde6ee;border-radius:8px;'
                      'padding:.4em .6em;text-align:center"><div style="color:#556;font-size:12px">%s</div><div style="font:bold '
                      '24px Arial,sans-serif;color:%s">%s</div><div style="color:#778;font-size:11px">%s</div></div>'
                      % x for x in (('floor', '#6A1B9A', '%.2f' % (fl * E4), '× 10⁻⁴ on 1 − F_B'),
                                    ('robust floor', '#2E7D32', '%.2f' % (rob * E4), 'any dephasing noise'),
                                    ('best duration of the bound', '#1B6F8C', '%.1f' % (1000 * T), 'ns')))
            + '</div><p style="font:13px/1.45 Arial,sans-serif">Pure dephasing accounts for <b>%.0f %%</b> of this floor. '
              'Move a slider: the floor follows in a fraction of a second (bounds only; the pulses are in the lab above).%s</p>'
            % (share, '' if not notes else ' T2 was clamped to 2 T1 for: %s.' % ', '.join(notes)))
    return K.result(card, [plot])
