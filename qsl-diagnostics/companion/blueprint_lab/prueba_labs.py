# encaje: prueba local de los laboratorios del blueprint qsl-diagnostics (controles conocidos y uno que debe fallar).
"""Known controls of the paper (Table V and RESULTADOS.md) and the controls that must FAIL. Run: python prueba_labs.py"""
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import qsl_diagnostics_lab as L  # noqa: E402
from qsl_data import J_MEDIAN  # noqa: E402

OK = True


def check(name, value, expected, tol):
    global OK
    good = abs(value - expected) <= tol
    OK &= good
    print('%-78s %s (value %.4f, expected %.4f)' % (name, 'OK' if good else 'FAIL', value, expected))


def must_fail(name, condition):
    """condition is the (false) claim; the control passes when the claim is rejected."""
    global OK
    OK &= not condition
    print('%-78s %s' % (name, 'OK (claim rejected)' if not condition else 'FAIL (false claim accepted)'))


# Table V, every row (log-log interpolation passes through the table's points)
for r, t in zip(L.R_TAB, L.T_TAB):
    check('Table V: r = %g gives T|delta|' % r, L.t_delta(r), t, 1e-9)
check('r = 0.1: T|delta| = 32.99 (the control asked for)', L.t_delta(0.1), 32.99, 1e-9)
check('IBM |delta| = 2.07 rad/ns, r = 0.1: about 16 ns (paper: ~16 ns)', 32.99 / 2.07, 16, 0.5)
check('IBM |delta| = 2.07 rad/ns, leakage floor 6.91: about 3.3 ns (paper: ~3.3 ns)', 6.91 / 2.07, 3.3, 0.1)
check('lab: r = 0.1 at 329.5 MHz (2.07 rad/ns) in ns', L.t_x_ns(0.1, 2.07 / L.DOS_PI * 1000), 15.94, 0.01)
check('Table V, column 3: T/(pi/Omega) at r = 0.1 is 1.05', L.t_delta(0.1) / (math.pi / 0.1), 1.05, 0.005)
check('Table V, column 3: T/(pi/Omega) at r = 0.5 is 1.30', L.t_delta(0.5) / (math.pi / 0.5), 1.30, 0.005)
check('exchange limit pi/(2J) at the median J = 0.0118 rad/ns (ns)', math.pi / (2 * 0.0118), 133.0, 0.3)
check('exchange limit pi/(2J) at the median J of the data (ns)', math.pi / (2 * J_MEDIAN), 133.2, 0.1)
_dc, _D = -L.rad_ns(330), L.rad_ns(100)
check('CR: r = 1, Delta/2pi = 100 MHz, |delta|/2pi = 330 MHz: (pi/2)/(J |dc/(dc+D)|) by hand',
      L.t_cr_ns(1.0, 100, 0.0118, 330), (math.pi / 2) / (0.0118 * abs(_dc / (_dc + _D))), 1e-9)
check('law at the crossing r = 1/2.2 equals both branches (T|delta|)', math.pi * 2.2, L.LEAK, 1e-9)

# the labs run and return what they promise
a = json.loads(L.run_fig1(json.dumps({'delta_mhz': 330, 'r': 0.1})))
check('run_fig1: r = 0.1 text carries 33.0 ... 32.99', float('32.99' in a['text']), 1.0, 0)
b = json.loads(L.run_fig2(json.dumps({})))
check('run_fig2: the text carries the 133.2 ns exchange limit', float('133.2' in b['text']), 1.0, 0)
c = json.loads(L.run_fig4(json.dumps({'r': 0.1})))
check('run_fig4: svg returned', float(c['plots'][0]['kind'] == 'svg'), 1.0, 0)
check('run_fig1: 3D with %d slider frames' % len(a['plots'][0]['slider']['items']),
      float(a['plots'][0]['kind'] == '3d'), 1.0, 0)
check('run_fig2: two 3D plots', float(len(b['plots'])), 2.0, 0)

# controls that must fail
must_fail('control: r = 0.05 (below the measured grid) is refused', 'error' not in json.loads(L.run_fig1(json.dumps({'r': 0.05}))))
must_fail('control: r = 3 (above the grid) is refused', 'error' not in json.loads(L.run_fig4(json.dumps({'r': 3}))))
must_fail('control: a detuning of 330 MHz (outside the range of the figure) is refused',
          'error' not in json.loads(L.run_fig2(json.dumps({'detuning_mhz': 330}))))
try:
    L.t_cr_ns(1.0, 330, 0.0118, 330)
    diverges = False
except ValueError:
    diverges = True
must_fail('control: Delta = |delta| (the first-order formula diverges) is refused by the formula', not diverges)
must_fail('control: a wrong claim, T|delta| at r = 0.1 is 31.4 (= pi/r), not the table value',
          abs(L.t_delta(0.1) - math.pi / 0.1) < 0.01)
must_fail('control: the law equals the table at r = 0.5 (paper: it is only a fit)',
          abs(max(math.pi / 0.5, L.LEAK) - L.t_delta(0.5)) < 0.1)
# the new labs: Figure 3, the d-level CZ, your device, the Bloch sphere
import qsl_bounds_lab as B  # noqa: E402
import qsl_series_lab as SE  # noqa: E402

f3 = json.loads(SE.run_fig3(json.dumps({})))
for y, v1, v2 in [('2021', 11.28, 2.78), ('2022', 11.32, 2.64), ('2023', 11.21, 4.32), ('2024', 11.10, 3.89),
                  ('2025', 11.87, 4.26)]:
    got = {(r[0][:6], r[2]): float(r[4]) for r in f3['table']['rows']}
    check('run_fig3: %s single-qubit median of medians (paper %.2f)' % (y, v1), got[('single', y)], v1, 0.005)
    check('run_fig3: %s two-qubit median of medians (paper %.2f)' % (y, v2), got[('two-qu', y)], v2, 0.005)
check('run_fig3: one 2D figure and two 3D panels by default', float(len(f3['plots'])), 3.0, 0)
f3t = json.loads(SE.run_fig3(json.dumps({'quantity': '2q', 'exclude': 'toronto'})))
check('run_fig3: without toronto the 2021 two-qubit median is 2.74 (paper)',
      float([r for r in f3t['table']['rows'] if r[2] == '2021'][0][4]), 2.74, 0.005)
must_fail('control: an unknown backend is refused', 'error' not in json.loads(SE.run_fig3(json.dumps({'exclude': 'zzz'}))))

check('lambda_3 = sqrt 3', B.lam(3), math.sqrt(3), 1e-9)
check('kappa_3 = 2 (|H_c| = 2J for d = 3)', B.kappa(3), 2.0, 1e-9)
check('kappa_2 = 1, lambda_2 = 1', B.kappa(2) + B.lam(2), 2.0, 1e-9)
for d, lo, up in [(4, 0.226725, 0.288246), (5, 0.160319, 0.192446), (10, 0.060939, 0.066519),
                  (20, 0.025699, 0.027059)]:
    check('d = %d: bound pi/(4 kappa_d) (paper table)' % d, math.pi / (4 * B.kappa(d)), lo, 1e-6)
    check('d = %d: construction pi/(2 lambda_d^2) (paper table)' % d, math.pi / (2 * B.lam(d) ** 2), up, 1e-6)
check('Lean bracket at d = 30: lambda^2/2 <= kappa <= 2(d-1)',
      float(B.lam(30) ** 2 / 2 <= B.kappa(30) <= 58), 1.0, 0)
q = json.loads(B.run_qudit(json.dumps({'d': 3})))
check('run_qudit: d = 3 text carries the refined 0.4511/J in ns', float('%.1f ns' % (0.4511064 / J_MEDIAN) in q['text']),
      1.0, 0)
must_fail('control: d = 1 is refused', 'error' not in json.loads(B.run_qudit(json.dumps({'d': 1}))))

dv = json.loads(B.run_device(json.dumps({'omega': 0.727, 'tx': 35.6, 'delta_mhz': 329.5})))
rat = {r[1]: float(r[3]) for r in dv['table']['rows']}
check('run_device: Falcon 35.6 ns at r_full 0.351 is 8.2x the exact two-level limit (paper 7.4-8.3)',
      rat['π/Ω_max (exact X)'], 8.24, 0.02)
check('run_device: the falsifier tolerance at e = 1e-4 is 0.991 of the exact limit',
      2 * math.asin(1 - 1e-4) / math.pi, 0.991, 0.0005)
must_fail('control: a gate below the floor is not flagged',
          'below the floor' not in json.loads(B.run_device(json.dumps({'tx': 3.0})))['text'])

for shape in ('square', 'sine', 'gaussian'):
    t = json.loads(B.run_bloch(json.dumps({'shape': shape})))['text']
    check('run_bloch: %s pi pulse, fixed axis: ratio 1 (equality case)' % shape, float('ratio <b>1.0000' in t), 1.0, 0)
t = json.loads(B.run_bloch(json.dumps({'shape': 'gaussian', 'beta': 1.0})))['text']
must_fail('control: with a DRAG quadrature the ratio is still 1', 'ratio <b>1.0000' in t)
t = json.loads(B.run_bloch(json.dumps({'shape': 'square', 'T': 10})))['text']
check('run_bloch: a square pi pulse is at the two-level limit (1.00x)', float('is 1.00× longer' in t), 1.0, 0)
# your own data: a list of gates, a pulse of your own
bt = json.loads(B.run_device(json.dumps({'batch': 'a, 0.5, 24, 0.012, 300\nb, 0.9, 3.0, , \nc, , , 0.02, 60'})))
check('run_device batch: three gates in the table', float(len(bt['table']['rows'])), 3.0, 0)
check('run_device batch: a 3 ns X at 0.9 rad/ns (ratio 0.86) fires the falsifier',
      float('Below the floor' in bt['text'] and 'b (single qubit' in bt['text']), 1.0, 0)
check('run_device batch: a single-qubit ratio by hand, 24*0.5/pi', float(bt['table']['rows'][0][3]),
      round(24 * 0.5 / math.pi, 2), 0)
ib = json.loads(B.run_device(json.dumps({'batch': 'ibm'})))
check('run_device batch ibm: 29 processors', float(len(ib['table']['rows'])), 29.0, 0)
must_fail('control: a line with four fields is refused',
          'error' not in json.loads(B.run_device(json.dumps({'batch': 'a, 1, 2, 3'}))))
t = json.loads(B.run_bloch(json.dumps({'shape': 'custom', 'samples': '0, 2, 5, 1, 4, 0'})))['text']
check('run_bloch custom: a positive envelope of your own still gives ratio 1', float('ratio <b>1.0000' in t), 1.0, 0)
t = json.loads(B.run_bloch(json.dumps({'shape': 'custom', 'samples': '0, 3, -1, 3, 0'})))['text']
must_fail('control: an envelope that changes sign still gives ratio 1', 'ratio <b>1.0000' in t)
# Section VIII (version 2): the relay lab against the paper and the companion package (relevo/lindblad_rk4.py: 0.1289 %)
import qsl_relay_lab as RL  # noqa: E402
check('relay: master-equation error at the minimal time, Q240–Q247 at 9 MHz (%)',
      100 * RL.lindblad_error(1 / (2 * math.sqrt(2) * 9.0), 121.0, 14.0, 28.8, 36.0), 0.1289, 0.00051)
rr = json.loads(RL.run_relay(json.dumps({'g_mhz': '9', 'tg_ns': '312', 't1q': '121', 't2q': '14', 't1c': '28.8',
                                         't2c': '36', 'measured': '0.71'})))
check('relay: T_g/T_min = 7.94 (Table VII)', float(rr['table']['rows'][1][2]), 7.94, 0)
check('relay: IBM additive model 0.625 % on Q240–Q247 (paper: 0.63 %)', float('0.625 %' in rr['text']), 1.0, 0)
check('relay: qubit dephasing dominates at 56 % (IBM: «56 to 76 %»)', float('qubit dephasing (T2 of the qubits) gives 56 %' in rr['text']), 1.0, 0)
check('relay: coherence explains 88 % of the measured 0.71 %', float('explains 88 %' in rr['text']), 1.0, 0)
must_fail('control: T2 > 2 T1 is accepted', 'error' not in json.loads(RL.run_relay(json.dumps(
    {'g_mhz': '9', 'tg_ns': '312', 't1q': '10', 't2q': '30', 't1c': '28', 't2c': '36'}))))
check('relay: closed first-order form (identity R1) against the master equation, Q240–Q247 (%)',
      100 * RL.first_order_error(9.0, 121.0, 14.0, 28.8, 36.0), 0.1289, 0.0005)
check('relay: the 3D figure is there with its slider (4 cable values)',
      float(rr['plots'][0].get('kind') == '3d' and len(rr['plots'][0]['slider']['values']) == 4), 1.0, 0)
must_fail('control: the first-order form at twice g is not half the error',
          abs(RL.first_order_error(18.0, 121.0, 14.0, 28.8, 36.0) / RL.first_order_error(9.0, 121.0, 14.0, 28.8, 36.0) - 0.5) > 1e-12)
for _ in range(5):
    d = json.loads(RL.random_relay())
    out = json.loads(RL.run_relay(json.dumps(d)))
    check('relay dice: %s MHz, %s ns runs and explains' % (d['g_mhz'], d['tg_ns']),
          float('error' not in out and 'Reading.' in out['text']), 1.0, 0)
print('ALL LAB CHECKS:', 'PASS' if OK else 'FAIL')
