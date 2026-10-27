# encaje: comprobación de las cifras del blueprint qsl-diagnostics contra las salidas archivadas del companion.
"""Recomputes, from the archived outputs of the reproducible package (barrido.csv, pares.csv, serie.csv), the numbers
that the commentary of the blueprint quotes, and compares them with the numbers printed in the paper. Each check has a
control that must FAIL (a check that cannot fail checks nothing). Run from anywhere; the package path is below."""
import csv
import math
import statistics as st
import sys
from pathlib import Path

PKG = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[1] / 'files'  # unpacked package
OK = True


def check(name, value, expected, tol):
    global OK
    good = abs(value - expected) <= tol
    OK &= good
    print('%-70s %s (value %.4f, paper %.4f)' % (name, 'OK' if good else 'FAIL', value, expected))


def control(name, value, expected, tol):
    """A check that must FAIL: the wrong expected value must be rejected."""
    global OK
    rejected = abs(value - expected) > tol
    OK &= rejected
    print('%-70s %s (value %.4f vs wrong %.4f)' % (name, 'OK (rejected)' if rejected else 'FAIL (accepted)',
                                                   value, expected))


def pct(v, q):
    v = sorted(v)
    k = (len(v) - 1) * q
    f = int(k)
    return v[f] + (v[min(f + 1, len(v) - 1)] - v[f]) * (k - f)


rows = list(csv.DictReader(open(PKG / 'barrido.csv', encoding='utf8')))
rx = [float(r['rx']) for r in rows]
check('single qubit: number of qubits (barrido.csv)', len(rows), 1646, 0)
check('single qubit: median tau_X/tau_QSL', st.median(rx), 11.30, 0.01)
check('single qubit: 5th percentile', pct(rx, 0.05), 7.19, 0.02)
check('single qubit: 95th percentile', pct(rx, 0.95), 15.54, 0.02)
check('single qubit: minimum', min(rx), 2.37, 0.01)
check('single qubit: sqrt(X) median ratio', st.median(float(r['rsx']) for r in rows), 22.61, 0.01)
check('single qubit: leakage periods tau_X/(2pi/|delta|), median', st.median(float(r['fuga']) for r in rows), 15.45,
      0.02)
control('control: a median of 5 is rejected', st.median(rx), 5.0, 0.01)

pairs = list(csv.DictReader(open(PKG / 'pares.csv', encoding='utf8')))
jq = [float(r['jq']) for r in pairs]
ratio = [float(r['t']) * float(r['jq']) / (math.pi / 2) for r in pairs]
check('two qubits: number of pairs (pares.csv)', len(pairs), 1758, 0)
check('two qubits: backends', len({r['backend'] for r in pairs}), 43, 0)
check('two qubits: ECR pairs', sum(r['gate'] == 'ecr' for r in pairs), 1019, 0)
check('two qubits: CX pairs', sum(r['gate'] == 'cx' for r in pairs), 739, 0)
check('two qubits: median j_q (rad/ns)', st.median(jq), 0.01268, 0.00001)
check('two qubits: median duration (ns)', st.median(float(r['t']) for r in pairs), 548, 1)
check('two qubits: median ratio to pi/(2 j_q)', st.median(ratio), 4.22, 0.01)
check('two qubits: certified chord ratio, median of t*j_q/sqrt(2-sqrt2)',
      st.median(float(r['t']) * float(r['jq']) / math.sqrt(2 - math.sqrt(2)) for r in pairs), 8.7, 0.05)
check('exchange limit pi/(2 j_q) at the median j_q (ns)', math.pi / (2 * st.median(jq)), 124.0, 1.0)
control('control: a ratio of 2 is rejected', st.median(ratio), 2.0, 0.01)

ser = list(csv.DictReader(open(PKG / 'serie.csv', encoding='utf8')))
check('time series: usable snapshots (serie.csv)', len(ser), 56, 0)
by = {}
for r in ser:
    by.setdefault(r['fecha'][:4], []).append(r)
paper = {'2021': (11.28, 2.78), '2022': (11.32, 2.64), '2023': (11.21, 4.32), '2024': (11.10, 3.89),
         '2025': (11.87, 4.26)}
for y, (p1, p2) in paper.items():
    check('time series %s: single-qubit median of medians' % y, st.median(float(r['rx_med']) for r in by[y]), p1, 0.01)
    check('time series %s: two-qubit median of medians' % y,
          st.median(float(r['r2_med']) for r in by[y] if r['r2_med']), p2, 0.01)
control('control: the 2025 two-qubit value is not the 2021 one',
        st.median(float(r['r2_med']) for r in by['2025'] if r['r2_med']),
        2.78, 0.01)
print('ALL NUMBERS:', 'PASS' if OK else 'FAIL')
