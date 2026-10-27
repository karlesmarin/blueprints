# encaje: serie temporal de las instantáneas de IBM a través de versiones de Qiskit (qsl-hardware): descarga, extrae
# (backend, fecha) únicos y calcula tau_X/tau_QSL y tau_2q/(pi/(2 jq)) con las reglas de barrido.py; investigación.
"""Versions: qiskit-terra (fake_provider/backends/*/props_*.json, conf_*.json) and qiskit-ibm-runtime
(fake_provider/backends/...). Each snapshot is keyed by (backend, last_update_date) and kept once; the source package
and version are recorded. Rules as in barrido.py: drop a snapshot with dt >= 1 ns; drop qubits with delta = 0.
Outputs datos_serie/ (json copies, Apache 2.0) and serie.csv."""
import csv
import json
import re
import shutil
import subprocess
import sys
import tarfile
import zipfile
from pathlib import Path

import numpy as np

AQUI = Path(__file__).parent
TMP = AQUI / 'cache_pip'   # downloaded Qiskit packages (not distributed; the extracted snapshots are in datos_serie/)
VERSIONES = [('qiskit-terra', v) for v in ('0.16.4', '0.18.3', '0.20.2', '0.22.4', '0.24.1', '0.25.3')] + \
            [('qiskit-ibm-runtime', v) for v in ('0.20.0', '0.25.0', '0.30.0', '0.35.0', '0.40.0', '0.45.0', '0.51.0')]
DEST = AQUI / 'datos_serie'


def bajar(pkg, ver):
    d = TMP / f'{pkg}-{ver}'
    if d.exists():
        return d
    d.mkdir(parents=True)
    r = subprocess.run([sys.executable, '-m', 'pip', 'download', f'{pkg}=={ver}', '--no-deps', '--no-binary', ':none:',
                        '-d', str(d)], capture_output=True, text=True)
    if r.returncode:
        print('FALLO descarga', pkg, ver, r.stderr[-300:])
        return None
    for f in d.iterdir():
        if f.suffix == '.whl':
            zipfile.ZipFile(f).extractall(d / 'x')
        elif f.name.endswith('.tar.gz'):
            with tarfile.open(f) as t:
                t.extractall(d / 'x', filter='data')
    return d


instantaneas = {}
for pkg, ver in VERSIONES:
    d = bajar(pkg, ver)
    if not d:
        continue
    for props in (d / 'x').rglob('props_*.json'):
        nombre = props.stem[len('props_'):]
        conf = props.with_name(f'conf_{nombre}.json')
        if not conf.exists():
            continue
        try:
            p = json.loads(props.read_text())
        except Exception as e:
            print('json', props, e)
            continue
        fecha = p.get('last_update_date', '')[:10]
        clave = (nombre, fecha)
        if clave not in instantaneas:
            instantaneas[clave] = (props, conf, f'{pkg} {ver}')
print(f'instantáneas únicas (backend, fecha): {len(instantaneas)}')

DEST.mkdir(exist_ok=True)
filas = []
for (nombre, fecha), (props, conf, fuente) in sorted(instantaneas.items(), key=lambda kv: kv[0][1]):
    sub = DEST / f'{nombre}_{fecha}'
    sub.mkdir(exist_ok=True)
    shutil.copy(props, sub / props.name)
    shutil.copy(conf, sub / conf.name)
    c, p = json.loads(conf.read_text()), json.loads(props.read_text())
    v = (c.get('hamiltonian') or {}).get('vars', {})
    if not v or c.get('dt', 0) >= 1:
        continue
    tx, t2 = {}, {}
    for g in p['gates']:
        L = [x['value'] for x in g['parameters'] if x['name'] == 'gate_length']
        if not L:
            continue
        if g['gate'] == 'x' and len(g['qubits']) == 1:
            tx[g['qubits'][0]] = L[0]
        if g['gate'] in ('cx', 'ecr', 'cz') and len(g['qubits']) == 2:
            k = tuple(sorted(g['qubits']))
            t2[k] = min(t2.get(k, 1e9), L[0])
    rx = [tx[q] / (np.pi / v[f'omegad{q}']) for q in tx
          if v.get(f'omegad{q}') and v.get(f'delta{q}')]
    r2 = []
    for k, val in v.items():
        m = re.fullmatch(r'jq(\d+)q(\d+)', k)
        if m and val:
            par = tuple(sorted((int(m.group(1)), int(m.group(2)))))
            if par in t2:
                r2.append(t2[par] / (np.pi / (2 * val)))
    if rx:
        filas.append(dict(backend=nombre, fecha=fecha, fuente=fuente, n1=len(rx), rx_med=float(np.median(rx)),
                          tx_med=float(np.median(list(tx.values()))), n2=len(r2),
                          r2_med=float(np.median(r2)) if r2 else None))

with open(AQUI / 'serie.csv', 'w', newline='', encoding='utf-8') as f:
    w = csv.DictWriter(f, fieldnames=list(filas[0]))
    w.writeheader()
    w.writerows(filas)
print(f'instantáneas útiles: {len(filas)} de {len({f["backend"] for f in filas})} backends')
print(f'{"fecha":10s} {"backend":13s} {"n1":>4s} {"tauX":>6s} {"X/QSL":>6s} {"2q/QSL":>7s}  fuente')
for r in filas:
    print(f'{r["fecha"]:10s} {r["backend"]:13s} {r["n1"]:4d} {r["tx_med"]:6.1f} {r["rx_med"]:6.2f} '
          f'{r["r2_med"] if r["r2_med"] else float("nan"):7.2f}  {r["fuente"]}')
años = {}
for r in filas:
    años.setdefault(r['fecha'][:4], []).append(r)
print('\nPor año (mediana de las medianas):')
for a in sorted(años):
    rs = años[a]
    r2 = [r['r2_med'] for r in rs if r['r2_med']]
    print(f'  {a}: {len(rs):3d} instantáneas · X/QSL {np.median([r["rx_med"] for r in rs]):.2f} · '
          f'2q/QSL {np.median(r2) if r2 else float("nan"):.2f}')
