"""Validación del cohete con Heya et al. (IBM), arXiv:2502.15034v2: transferencia SATD por una CPW de 60 cm.
# encaje: control de la misión relevo (qsl-hardware); usa lindblad_relevo con el pulso PUBLICADO.

Datos (comprobados en el PDF, fuentes/heya2025/): ecs. (1)–(3) (imagen de la p. 3):
  g_e = g[sin θ + θ̈ cos θ/(g² + θ̇²)], g_r = g[cos θ − θ̈ sin θ/(g² + θ̇²)], θ = (π/2)(6s⁵ − 15s⁴ + 10s³), s = t/T;
  g/2π = 3,5 MHz, T = 135 ns (p. 4); secuencia entera 206 ns (p. 5). Tabla I (p. 9): QL1 T1 = 113 µs,
  T2,Ramsey = 18 µs; QL2 T1 = 76, T2 = 22; modo m = 50 T1 = 5,23 µs (T2 del modo no dado: sin desfase puro).
Sus simulaciones (Supl., «Error budget»): a 206 ns, toy1 multimodo: solo pérdida del CPW ≈ 2·10⁻³; todo ≈ 0,0062.
SUPUESTO nuestro: un solo modo (dicen que los espectadores son despreciables a 206 ns) y la excitación quieta en el
emisor/receptor durante (206 − 135)/2 ns antes y después (rampas de frecuencia, regiones 1–3 y 5–7).
"""
import argparse
import math
import numpy as np
from lindblad_relevo import disipadores, fidelidad_media, A, B


def tramos_satd(g, T, n):
    dt = T / n
    out = []
    for k in range(n):
        s = (k + 0.5) / n
        th = math.pi / 2 * (6 * s ** 5 - 15 * s ** 4 + 10 * s ** 3)
        thd = math.pi / 2 * (30 * s ** 4 - 60 * s ** 3 + 30 * s ** 2) / T
        thdd = math.pi / 2 * (120 * s ** 3 - 180 * s ** 2 + 60 * s) / T ** 2
        ge = g * (math.sin(th) + thdd * math.cos(th) / (g ** 2 + thd ** 2))
        gr = g * (math.cos(th) - thdd * math.sin(th) / (g ** 2 + thd ** 2))
        out.append((dt, ge, gr))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('caso', choices=['unitario', 'cpw', 'todo'])
    ap.add_argument('--n', type=int, default=200)
    ap.add_argument('--espera', type=float, default=(0.206 - 0.135) / 2, help='µs en cada cúbit fuera de la región 4')
    a = ap.parse_args()
    g, T = 2 * math.pi * 3.5, 0.135
    tr = tramos_satd(g, T, a.n)
    inf = 1e12
    if a.caso == 'unitario':
        Ls = []
    elif a.caso == 'cpw':
        Ls = disipadores(dict(a=inf, b=inf, c=5.23), dict(a=2 * inf, b=2 * inf, c=2 * 5.23))
    else:
        Ls = disipadores(dict(a=113.0, b=76.0, c=5.23), dict(a=18.0, b=22.0, c=2 * 5.23))
    tr = [(a.espera, 0.0, 0.0)] + tr + [(a.espera, 0.0, 0.0)] if a.caso == 'todo' else tr
    F = fidelidad_media(tr, Ls, A, B)
    print(f'Heya SATD {a.caso}: infidelidad = {1 - F:.3e}')


if __name__ == '__main__':
    main()
