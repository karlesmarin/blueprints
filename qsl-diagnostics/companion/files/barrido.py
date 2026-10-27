# encaje: pruebas «razones» y «correlacion» de ficha_ideas.toml sobre todas las instantáneas de IBM (datos/); investigación.
"""Per qubit: omegad (rad/ns, convention fixed by pulsos_x.py: Rabi frequency omegad*|D|), delta (rad/ns), durations
of x and sx (ns). Speed limits at full amplitude: X needs pi/omegad, SX needs pi/(2 omegad) (Mandelstam–Tamm in the
two-level rotating frame, saturated by a square pulse). Leakage scale: 2 pi/|delta|.
Writes barrido.csv and prints a summary per backend and global. Controls: armonk by hand (2.631); changing omegad
from rad/ns to GHz must move the median by 2 pi (negative control)."""
import csv
import json
import statistics as st
from pathlib import Path

import numpy as np

DATOS = Path(__file__).parent / 'datos'


def leer(nombre):
    c = json.loads((DATOS / nombre / f'conf_{nombre}.json').read_text())
    p = json.loads((DATOS / nombre / f'props_{nombre}.json').read_text())
    return c, p


def duraciones(props, puerta):
    out = {}
    for g in props['gates']:
        if g['gate'] == puerta and len(g['qubits']) == 1:
            v = [x['value'] for x in g['parameters'] if x['name'] == 'gate_length']
            if v:
                out[g['qubits'][0]] = v[0]
    return out


filas = []
for b in sorted(d.name for d in DATOS.iterdir() if d.is_dir()):
    try:
        c, p = leer(b)
    except FileNotFoundError:
        continue
    vars_ = (c.get('hamiltonian') or {}).get('vars', {})
    # 27-oct: the falsifier (ratio < 1) flagged brussels and strasbourg (2026): dt = 4 ns instead of 0.222, omegad
    # ~58 times smaller, qubits with delta exactly 0 -> placeholder Hamiltonians, not calibration data
    # rule: the whole backend out if dt >= 1 ns (synthetic 4-ns snapshots); a single qubit out if its delta is 0
    if c.get('dt', 0) >= 1 and vars_:
        print(f'EXCLUIDO {b}: dt = {c.get("dt")} ns (instantánea sintética)')
        continue
    tx, tsx = duraciones(p, 'x'), duraciones(p, 'sx')
    fecha = p.get('last_update_date', '')[:10]
    for q in range(c.get('n_qubits', 0)):
        om, de = vars_.get(f'omegad{q}'), vars_.get(f'delta{q}')
        if not om or q not in tx or not de:
            continue
        filas.append(dict(backend=b, fecha=fecha, qubit=q, omegad=om, delta=de, tx=tx[q], tsx=tsx.get(q),
                          rx=tx[q] / (np.pi / om), rsx=(tsx[q] / (np.pi / (2 * om)) if q in tsx else None),
                          fuga=(tx[q] / (2 * np.pi / abs(de)) if de else None)))

with open(Path(__file__).parent / 'barrido.csv', 'w', newline='', encoding='utf-8') as f:
    w = csv.DictWriter(f, fieldnames=list(filas[0]))
    w.writeheader()
    w.writerows(filas)

rx = np.array([r['rx'] for r in filas])
print(f'backends con Hamiltoniano y duraciones: {len({r["backend"] for r in filas})}; cúbits: {len(filas)}')
arm = [r for r in filas if r['backend'] == 'armonk'][0]
print(f'control + armonk: rx = {arm["rx"]:.3f} (a mano 2.631)', 'OK' if abs(arm['rx'] - 2.631) < 0.002 else 'FALLA')
rx_ghz = np.array([r['tx'] / (np.pi / (r['omegad'] / (2 * np.pi))) for r in filas])
print(f'control - (omegad en GHz): mediana {np.median(rx_ghz):.4f} vs {np.median(rx):.4f}, cociente '
      f'{np.median(rx) / np.median(rx_ghz):.4f} (esperado 2 pi = 6.2832)')
print(f'\nX : tau/tau_QSL  mediana {np.median(rx):.2f}  [p5 {np.percentile(rx, 5):.2f}, p95 {np.percentile(rx, 95):.2f}]  '
      f'min {rx.min():.2f}  · cúbits con razón < 1: {(rx < 1).sum()}')
rsx = np.array([r['rsx'] for r in filas if r['rsx']])
print(f'SX: tau/tau_QSL  mediana {np.median(rsx):.2f}  [p5 {np.percentile(rsx, 5):.2f}, p95 {np.percentile(rsx, 95):.2f}]')
fu = np.array([r['fuga'] for r in filas if r['fuga']])
print(f'X frente a la escala de fuga 2pi/|delta|: mediana {np.median(fu):.2f}  [p5 {np.percentile(fu, 5):.2f}, '
      f'p95 {np.percentile(fu, 95):.2f}]')

# correlation test (within backends, where the pulse duration is common: does omegad or |delta| explain the spread?)
print('\nPor backend (duración X común; ¿qué varía con el cúbit?):')
print(f'{"backend":13s} {"fecha":10s} {"n":>4s} {"tau_x":>7s} {"rx med":>7s} {"rx min":>7s} {"rx max":>7s} '
      f'{"fuga med":>8s}')
for b in sorted({r['backend'] for r in filas}):
    rs = [r for r in filas if r['backend'] == b]
    v = [r['rx'] for r in rs]
    fg = [r['fuga'] for r in rs if r['fuga']]
    print(f'{b:13s} {rs[0]["fecha"]:10s} {len(rs):4d} {st.median(r["tx"] for r in rs):7.1f} {st.median(v):7.2f} '
          f'{min(v):7.2f} {max(v):7.2f} {st.median(fg) if fg else float("nan"):8.2f}')

# across all qubits: log tau_x against log(1/omegad) and log(1/|delta|)
lt = np.log([r['tx'] for r in filas if r['delta']])
lo = np.log([1 / r['omegad'] for r in filas if r['delta']])
ld = np.log([1 / abs(r['delta']) for r in filas if r['delta']])
r2 = lambda a, b: float(np.corrcoef(a, b)[0, 1] ** 2)
rng = np.random.default_rng(0)
print(f'\nR^2 log tau_x ~ log(1/omegad): {r2(lt, lo):.3f} · ~ log(1/|delta|): {r2(lt, ld):.3f} · '
      f'control barajado: {r2(rng.permutation(lt), lo):.3f}')
