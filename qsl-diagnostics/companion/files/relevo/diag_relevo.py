"""Diagnóstico de un relevo cúbit → modo → cúbit a partir de un fichero de datos (relevo/datos/*.toml).
# encaje: módulo de la misión relevo (qsl-hardware); datos aparte (TOML), cálculo aquí, réplica en lindblad_relevo.py.

Órdenes:
  modelo  <datos> <enlace>          error del modelo de IBM (ec. 1–2) a T_g con las ocupaciones del fichero
  suelo   <datos> <enlace> <gMHz>   ídem al óptimo π/(√2 g) con ocupaciones (¾ cúbits, ¼ cable)
  tabla   <datos>                   cocientes T_g/T_min y suelos de todos los enlaces
"""
import math
import sys
import tomllib
from lindblad_relevo import ec1


def cargar(ruta):
    with open(ruta, 'rb') as f:
        return tomllib.load(f)


def enlace(d, nombre):
    return next(e for e in d['enlace'] if e['nombre'] == nombre)


def error_ocupacion(T_ns, fq, fc, e):
    T = T_ns / 1000
    return ec1(fq * T, e['T1q'], e['T2q']) + ec1(fc * T, e['T1c'], e['T2c'])


def t_min(gMHz):
    return 1000 / (2 * math.sqrt(2) * gMHz)                  # π/(√2·2π·g/2π) en ns


def main(argv):
    orden, d = argv[0], cargar(argv[1])
    if orden == 'modelo':
        e = enlace(d, argv[2]); fq, fc = d['ocupacion_modelo']
        print(f"modelo {e['nombre']} = {100 * error_ocupacion(e['Tg'], fq, fc, e):.4f} % "
              f"(IBM: {100 - e['F_modelo']:.2f} %)")
    elif orden == 'suelo':
        e = enlace(d, argv[2]); g = float(argv[3])
        print(f"suelo {e['nombre']} {g} MHz = {100 * error_ocupacion(t_min(g), 0.75, 0.25, e):.4f} %")
    elif orden == 'tabla':
        for e in d['enlace']:
            r = [e['Tg'] / t_min(g) for g in d['g_MHz']]
            s = [100 * error_ocupacion(t_min(g), 0.75, 0.25, e) for g in d['g_MHz']]
            print(f"{e['nombre']}: T_g {e['Tg']} ns, T_g/T_min {min(r):.2f}–{max(r):.2f}, error {100 - e['F']:.2f} %, "
                  f"suelo {min(s):.4f}–{max(s):.4f} %")


if __name__ == '__main__':
    main(sys.argv[1:])
