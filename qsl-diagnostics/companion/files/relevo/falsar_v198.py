"""Verificación propia de dos afirmaciones de V198 (el compañero): son hipótesis hasta que este script las confirme.
# encaje: control de investigación (qsl-hardware, relevo); usa lindblad_relevo.

(1) Primer orden: 1 − F = (1/3) ∫ Σ_j [γ1_j p_j + γφ_j (2 p_j − p_j²)] dt (frente al aditivo de IBM: γφ_j p_j).
(2) Contraejemplo: cable sin pérdida, cúbits con γq: protocolo rápido D = 3π/(4√2)·γ/G ≈ 1,666 γ/G frente a
    secuencial π/2·γ/G ≈ 1,571 γ/G (D = exposición ∫ γ(p_A + p_B) dt). Se comprueba también con la infidelidad real.
"""
import math
import numpy as np
from lindblad_relevo import disipadores, fidelidad_media, evolucionar, ket, A, B, C


def poblaciones(tramos, sub=40):
    rho = np.outer(ket(A), ket(A)); out = []
    for dt, g1, g2 in tramos:
        for _ in range(sub):
            rho = evolucionar(rho, [(dt / sub, g1, g2)], [])
            out.append((dt / sub, [float(np.real(rho[j, j])) for j in (A, C, B)]))
    return out


def primer_orden(tramos, g1T1, gphi):
    tot = 0.0
    for dt, p in poblaciones(tramos):
        for k, pj in enumerate(p):
            tot += dt * (g1T1[k] * pj + gphi[k] * (2 * pj - pj ** 2))
    return tot / 3


def varianza(tramos, g1T1, gphi):
    """Nuestra: pérdida = ∫ Var(L) en el estado que evoluciona; media en 6 estados (⟨|β|²⟩ = ½, ⟨|β|⁴⟩ = ⅓):
    1 − F = ∫ Σ_j [γ1_j q_j/3 + γφ_j (q_j − ⅔ q_j²)] dt = aditivo + ⅔ Σ_j ∫ γφ_j q_j (1 − q_j) dt."""
    tot = 0.0
    for dt, p in poblaciones(tramos):
        for k, pj in enumerate(p):
            tot += dt * (g1T1[k] * pj / 3 + gphi[k] * (pj - 2 * pj ** 2 / 3))
    return tot


def aditivo(tramos, g1T1, gphi):
    tot = 0.0
    for dt, p in poblaciones(tramos):
        for k, pj in enumerate(p):
            tot += dt * (g1T1[k] + gphi[k]) * pj
    return tot / 3


g = 2 * math.pi * 9.0
T = math.pi / (math.sqrt(2) * g)
rapido = [(T / 4, g, g)] * 4
h = math.pi / (2 * g)
secuencial = [(h, g, 0.0), (h, 0.0, g)]
print('(1) primer orden, débil (T1 = T2/2 grandes):')
for nombre, T1, T2 in (('solo desfase cúbits', (1e9, 1e9, 1e9), (1400.0, 2e9, 1400.0)),
                       ('solo desfase cable', (1e9, 1e9, 1e9), (2e9, 3600.0, 2e9)),
                       ('relajación + desfase', (11260.0, 2880.0, 11260.0), (1400.0, 3600.0, 1400.0))):
    Ls = disipadores(dict(a=T1[0], c=T1[1], b=T1[2]), dict(a=T2[0], c=T2[1], b=T2[2]))
    g1T1 = [1 / t for t in T1]; gphi = [1 / t2 - 1 / (2 * t1) for t1, t2 in zip(T1, T2)]
    el = 1 - fidelidad_media(rapido, Ls, A, B)
    print(f'   {nombre:22s} Lindblad {el:.4e}  fórmula V198 {primer_orden(rapido, g1T1, gphi):.4e}  '
          f'varianza (nuestra) {varianza(rapido, g1T1, gphi):.4e}  aditivo {aditivo(rapido, g1T1, gphi):.4e}')
    # control: trayectoria distinta (secuencial) con el mismo ruido
    if nombre == 'relajación + desfase':
        el2 = 1 - fidelidad_media(secuencial, Ls, A, B)
        print(f'   {"  secuencial":22s} Lindblad {el2:.4e}  varianza (nuestra) {varianza(secuencial, g1T1, gphi):.4e}')
print('(2) exposición y error con pérdidas solo en cúbits (γ = 1/100 µs⁻¹):')
gq = 1 / 100.0
for nombre, tr in (('rápido', rapido), ('secuencial', secuencial)):
    D = sum(dt * gq * (p[0] + p[2]) for dt, p in poblaciones(tr))
    Ls = disipadores(dict(q=100.0, c=1e12), dict(q=200.0, c=2e12))
    print(f'   {nombre:10s} D·G/γ = {D * g / gq:.4f}   infidelidad Lindblad = {1 - fidelidad_media(tr, Ls, A, B):.4e}')
