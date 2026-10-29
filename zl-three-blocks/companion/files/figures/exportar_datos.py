# Writes data/*.json from datos.py.
import json
import shutil
import sys
from pathlib import Path

import datos

OUT = Path(__file__).resolve().parents[1] / 'datos'
OUT.mkdir(exist_ok=True)
sys.path.insert(0, str(datos.ZL))
import modulos_lambda as ML  # noqa: E402


def uno(c):
    return [x + 1 for x in c]


m, n, E1, E2, evita = datos.tres_bloques_22x5()
json.dump({'description': 'Three-block optimum for z_L(22,5) >= 52 (|E1| = z = 32, |E2| = 20). Cells (row, column), '
                          'from 1. Blocks A={1,2}, B={3,4}, C={5}; each row avoids the block in avoided_block.',
           'm': m, 'n': n, 'E1': sorted(uno(c) for c in E1), 'E2': [[uno(a), uno(b)] for a, b in E2],
           'avoided_block': ['ABC'[t] for t in evita]}, open(OUT / 'witness_22x5_three_blocks.json', 'w'), indent=1)

E1t, P, U = datos.tensor_3x3x5()
json.dump({'description': '3x3x5 box-graph configuration: maximum box-free base (34 cells), 3 admissible pairs, '
                          '5 empty cells; 4*|E2| = 12 > 11 = 45 - |E1|. Cells (i, j, k), from 1.',
           'E1': sorted(uno(c) for c in E1t), 'E2': [[uno(a), uno(b)] for a, b in P], 'empty': sorted(uno(c) for c in U)},
          open(OUT / 'witness_3x3x5_tensor.json', 'w'), indent=1)

mods = []
for nn in range(3, 13):
    mm, E1m, E2m, ppm, rpm = ML.construir(nn, 1)
    mods.append({'n': nn, 'blocks': [uno(b) for b in ML.bloques(nn)[0]], 'module_rows': rpm, 'module_pairs': ppm,
                 'lambda': str(ML.lam(nn)), 'example_m': mm, 'example_E1': sorted(uno(c) for c in E1m),
                 'example_E2': [[uno(a), uno(b)] for a, b in E2m]})
json.dump({'description': 'Block modules realizing lambda_n (one module plus the special rows); each example passes '
                          'both admissibility checkers.', 'modules': mods}, open(OUT / 'lambda_modules.json', 'w'), indent=1)

t = datos.tabla()
json.dump({'description': 'z_L(m,n): value, origin (published / new exact / bounds) and upper bound.',
           'entries': [{'m': a, 'n': b, 'zL': v, 'origin': o, 'upper': s} for (a, b), (v, o, s) in sorted(t.items())]},
          open(OUT / 'table_zL.json', 'w'), indent=1)
json.dump({'description': 'F_4(m) = z_L(m,4) - (m+6), exact, m = 6..40 (row-by-row search for m <= 14, type '
                          'reduction for all m).', 'F4': datos.f4()}, open(OUT / 'F4_exact.json', 'w'), indent=1)
for nn in (3, 4, 5, 6):
    shutil.copy(datos.ZL / f'cert_sombras_{nn}.json', OUT / f'shadow_certificate_n{nn}.json')
print(sorted(p.name for p in OUT.iterdir()))
