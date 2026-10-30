"""Cocientes de la transferencia de IBM (arXiv 2610.29986) frente a los tiempos mínimos del relevo cúbit–modo–cúbit.
# encaje: investigación (qsl-hardware v2); g/2π de 8 y 9 MHz (Fig. 1f), T_g de la Ext. Data Table 2.

Tiempos (g en rad/s = 2π · g/2π): cota Lean π/(2√2 g); óptimo π/(√2 g) (Boscain et al. 2005); secuencial π/g.
"""
import math

T_g = {'Q240–Q247': 312, 'Q241–Q246': 296, 'Q242–Q245': 256, 'Q243–Q244': 312, 'objetivo IBM': 126}
for gMHz in (8.0, 8.5, 9.0):
    g = 2 * math.pi * gMHz * 1e-3          # rad/ns
    lean, opt, seq = math.pi / (2 * math.sqrt(2) * g), math.pi / (math.sqrt(2) * g), math.pi / g
    print(f'g/2π = {gMHz} MHz: Lean {lean:.1f} ns, óptimo {opt:.1f} ns, secuencial {seq:.1f} ns')
    for k, T in T_g.items():
        print(f'   {k:13s} {T} ns: ×{T / opt:.2f} óptimo, ×{T / seq:.2f} secuencial, ×{T / lean:.1f} Lean')
