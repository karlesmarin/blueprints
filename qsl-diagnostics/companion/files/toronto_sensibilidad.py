# encaje: sensibilidad de la mediana anual de dos cúbits a la exclusión del snapshot degradado de toronto
# (2021-03-15; revisión externa 27-oct, punto 5.1); investigación, no herramienta.
import csv
from pathlib import Path

import numpy as np

filas = [f for f in csv.DictReader(open(Path(__file__).parent / 'serie.csv', encoding='utf-8')) if f['fecha'][:4] == '2021']
es_t = lambda f: f['backend'] == 'toronto' and f['fecha'] == '2021-03-15'
val = lambda f: float(f['r2_med']) if f['r2_med'] not in ('', 'nan') else None
con = [val(f) for f in filas if val(f) is not None]
sin = [val(f) for f in filas if val(f) is not None and not es_t(f)]
print(f'2021: con toronto-2021-03-15 {len(con)} snapshots, mediana {np.median(con):.2f}; '
      f'sin él {len(sin)}, mediana {np.median(sin):.2f}')
r1c = [float(f['rx_med']) for f in filas]
r1s = [float(f['rx_med']) for f in filas if not es_t(f)]
print(f'un cúbit 2021: con {np.median(r1c):.2f}, sin {np.median(r1s):.2f}')
