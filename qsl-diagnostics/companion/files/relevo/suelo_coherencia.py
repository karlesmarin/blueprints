"""Suelo de error por coherencia de la transferencia de IBM (arXiv 2610.29986) a su duración y al límite cuántico.
# encaje: investigación (qsl-hardware v2); modelo de IBM, ec. (1)-(2), con ocupaciones según el protocolo.

ε_el(t) = ½(1 − (e^{−t/T1} + 2 e^{−t/T2})/3) por elemento que retiene la excitación un tiempo t (IBM ec. 1).
Ocupaciones: IBM supone τ_q = τ_c = T_g/2. Protocolo simultáneo óptimo (g1 = g2 = g constantes): ∫p_c = T/4,
∫(p_A + p_B) = 3T/4. Secuencial a velocidad máxima: τ_q = τ_c = T/2. T1, T2 de las tablas extendidas 1 y 2
(para los cúbits, el más corto del par, como IBM).
"""
import math

enlaces = {   # (T_g ns, F medida %, F modelo IBM %, T1q, T2q, T1c, T2c) en µs; T1q/T2q = el más corto del par
    'Q240–Q247': (312, 99.29, 99.37, 121.0, 14.0, 28.8, 36.0),   # T1q: Q247 (antes 112,6 por error, era Q246)
    'Q241–Q246': (296, 98.87, 99.12, 99.7, 7.1, 38.6, 51.0),
    'Q242–Q245': (256, 98.99, 99.39, 146.3, 11.0, 22.7, 37.0),
    'Q243–Q244': (312, 98.86, 99.06, 112.0, 7.7, 24.8, 37.0),
}


def eps(t, T1, T2):
    return 0.5 * (1 - (math.exp(-t / T1) + 2 * math.exp(-t / T2)) / 3)


def error(T_ns, fq, fc, T1q, T2q, T1c, T2c):
    T = T_ns / 1000.0
    return eps(fq * T, T1q, T2q) + eps(fc * T, T1c, T2c)


print(f"{'enlace':10s} {'medido':>8s} {'IBM modelo':>10s} {'nuestro a Tg':>12s} | "
      f"{'QSL sim. 8MHz':>13s} {'QSL sim. 9MHz':>13s} {'secuencial 8.5':>14s}")
for k, (Tg, Fm, Fmod, T1q, T2q, T1c, T2c) in enlaces.items():
    e_ibm = error(Tg, 0.5, 0.5, T1q, T2q, T1c, T2c)
    t8 = 1000 / (2 * math.sqrt(2) * 8.0)        # ns
    t9 = 1000 / (2 * math.sqrt(2) * 9.0)
    tseq = 1000 / (2 * 8.5)
    e8 = error(t8, 0.75, 0.25, T1q, T2q, T1c, T2c)
    e9 = error(t9, 0.75, 0.25, T1q, T2q, T1c, T2c)
    es = error(tseq, 0.5, 0.5, T1q, T2q, T1c, T2c)
    print(f"{k:10s} {100 - Fm:7.3f}% {100 - Fmod:9.3f}% {100 * e_ibm:11.3f}% | "
          f"{100 * e8:12.4f}% {100 * e9:12.4f}% {100 * es:13.4f}%")

print("\nCon L-qubits T1 = T2 = 100 µs y el mejor cable (T1 = 38,6 µs, T2 = 51 µs):")
for nombre, T_ns, fq, fc in [('IBM 296 ns (½,½)', 296, .5, .5), ('IBM objetivo 126 ns (½,½)', 126, .5, .5),
                             ('QSL simultáneo 8,5 MHz (¾,¼)', 1000 / (2 * math.sqrt(2) * 8.5), .75, .25)]:
    print(f"  {nombre:32s} error = {100 * error(T_ns, fq, fc, 100, 100, 38.6, 51.0):.4f}%")
