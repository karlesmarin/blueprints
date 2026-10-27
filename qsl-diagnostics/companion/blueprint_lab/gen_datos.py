# encaje: generador (una sola vez) de lab/qsl_data.py, los puntos de los procesadores de IBM para los laboratorios.
"""Reuses chips() of the paper's own figure script (companion/paper/figuras_3d.py, executed only up to the line
`C = chips()`, so that no figure of the paper is rewritten) and writes the per-backend medians as plain Python numbers
for the labs (Pyodide has no numpy). Adds the time series (serie.csv, the rows behind Figure 3) with each snapshot's
qubit count and dominant two-qubit gate, read from the archived configuration (datos_serie/). Run once:
python gen_datos.py [unpacked package]"""
import csv
import json
import sys
from pathlib import Path

import numpy as np

PKG = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[1] / 'files'  # unpacked package
SRC = (PKG / 'paper' / 'figuras_3d.py').read_text(encoding='utf8')
head = SRC[:SRC.index('C = chips()')]
ns = {'__file__': str(PKG / 'paper' / 'figuras_3d.py'), '__name__': 'figuras_head'}
exec(compile(head, 'figuras_3d_head', 'exec'), ns)
C = ns['chips']()
J = float(np.median([ch['dos'][3] for ch in C]))
rows = []
for ch in C:
    de, r1, tau = (float(x) for x in ch['uno'])
    rcr, dl, tcx, jq = (float(x) for x in ch['dos'])
    rows.append((ch['b'], round(de, 6), round(r1, 6), round(tau, 4), round(rcr, 6), round(dl, 6), round(tcx, 4),
                 round(jq, 6)))


def snapshot_meta(backend, fecha):
    """(n_qubits, dominant two-qubit gate) of one archived snapshot (as serie_porque.py)."""
    sub = PKG / 'datos_serie' / ('%s_%s' % (backend, fecha))
    conf = json.loads(next(sub.glob('conf_*.json')).read_text())
    props = json.loads(next(sub.glob('props_*.json')).read_text())
    gates = [g['gate'] for g in props['gates'] if g['gate'] in ('cx', 'ecr', 'cz') and len(g['qubits']) == 2]
    return conf.get('n_qubits'), (max(set(gates), key=gates.count) if gates else '')


serie = []
for r in csv.DictReader(open(PKG / 'serie.csv', encoding='utf8')):
    nq, gate = snapshot_meta(r['backend'], r['fecha'])
    serie.append((r['backend'], r['fecha'], nq, gate, round(float(r['rx_med']), 4),
                  round(float(r['r2_med']), 4) if r['r2_med'] else None))

out = ['# encaje: datos de los laboratorios del blueprint qsl-diagnostics (medianas por procesador de IBM).',
       '"""Per-backend medians from the pulse definitions of qiskit-terra 0.24.1 (Apache 2.0), computed by chips() of',
       'companion/paper/figuras_3d.py (see gen_datos.py). Columns of CHIPS: backend, |delta| (rad/ns), Omega_peak/|delta|',
       '(one qubit), X duration (ns), Omega_CR/Delta, |Delta| (rad/ns), CX duration (ns), j_q (rad/ns). SERIE: the 56',
       'usable snapshots of serie.csv (Figure 3): backend, date, qubit count, dominant two-qubit gate, median',
       'tau_X/tau_QSL, median two-qubit ratio to pi/(2 j_q) (None: no two-qubit data). Generated file."""',
       'J_MEDIAN = %r' % round(J, 6), 'CHIPS = [']
out += ['    %r,' % (r,) for r in rows]
out.append(']')
out.append('SERIE = [')
out += ['    %r,' % (s,) for s in serie]
out.append(']')
(Path(__file__).parent / 'qsl_data.py').write_text('\n'.join(out) + '\n', encoding='utf8')
print(len(rows), 'processors; median J = %.6f rad/ns; exchange limit %.1f ns' % (J, np.pi / (2 * J)))
print(len(serie), 'snapshots; families', sorted({(s[2], s[3]) for s in serie}, key=str))
