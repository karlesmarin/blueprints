"""¿Por qué Lindblad da más error que el modelo de ocupaciones al óptimo? Separar relajación y desfase.
# encaje: diagnóstico de investigación (qsl-hardware, relevo); usa lindblad_relevo y diag_relevo.
"""
import math
from lindblad_relevo import disipadores, fidelidad_media, A, B
from diag_relevo import error_ocupacion

g = 2 * math.pi * 9.0
T = math.pi / (math.sqrt(2) * g)
casos = {
    'IBM Q240–Q247': dict(T1q=121.0, T2q=14.0, T1c=28.8, T2c=36.0),
    'solo relajación (T2 = 2T1)': dict(T1q=121.0, T2q=242.0, T1c=28.8, T2c=57.6),
    'solo desfase (T1 = 1e9)': dict(T1q=1e9, T2q=14.0, T1c=1e9, T2c=36.0),
    'desfase solo en el cable': dict(T1q=1e9, T2q=2e9, T1c=1e9, T2c=36.0),
    'desfase solo en cúbits': dict(T1q=1e9, T2q=14.0, T1c=1e9, T2c=2e9),
}
for n, e in casos.items():
    Ls = disipadores(dict(q=e['T1q'], c=e['T1c']), dict(q=e['T2q'], c=e['T2c']))
    for trozos in (1,):
        el = 100 * (1 - fidelidad_media([(T / trozos, g, g)] * trozos, Ls, A, B))
    eo = 100 * error_ocupacion(1000 * T, 0.75, 0.25, e)
    print(f'{n:28s} Lindblad {el:.5f} %  ocupación {eo:.5f} %  cociente {el / eo:.3f}')
