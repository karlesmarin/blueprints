"""Suelo de error por coherencia al tiempo mínimo π/(√2 g), dinámica entera (Lindblad) frente al modelo aditivo de IBM,
para todos los enlaces y valores de g de un fichero de datos.
# encaje: módulo de la misión relevo (qsl-hardware); usa lindblad_relevo y diag_relevo.
Uso: python suelo_lindblad.py datos/ibm_2610.29986.toml
"""
import math
import sys
from lindblad_relevo import disipadores, fidelidad_media, A, B
from diag_relevo import cargar, error_ocupacion, t_min

d = cargar(sys.argv[1])
for e in d['enlace']:
    Ls = disipadores(dict(q=e['T1q'], c=e['T1c']), dict(q=e['T2q'], c=e['T2c']))
    fila = []
    for gM in d['g_MHz']:
        g = 2 * math.pi * gM
        T = math.pi / (math.sqrt(2) * g)
        el = 100 * (1 - fidelidad_media([(T, g, g)], Ls, A, B))
        eo = 100 * error_ocupacion(t_min(gM), 0.75, 0.25, e)
        fila.append(f'{gM} MHz: Lindblad {el:.4f} % (aditivo {eo:.4f} %)')
    print(f"{e['nombre']}: " + ' | '.join(fila))
