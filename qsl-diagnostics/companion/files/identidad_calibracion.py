# encaje: busca la fórmula exacta con la que IBM fija omegad a partir del pulso pi calibrado (identidad 2 de qsl-hardware):
# qué normalización del área hace theta/pi constante en sigma; investigación, no herramienta.
"""Data: K(sigma) = omegad * |amp| * sigma * dt is identical across backends for equal sigma (9 digits). With our lifted
discrete area theta/pi = 1.14281 (sigma 24), 1.14820 (40), 1.15233 (80): not constant. Try candidate areas A(sigma,
duration = 4 sigma) and report theta/pi = K * A / (sigma * pi) per sigma; the right normalisation makes it CONSTANT
(and ideally a recognisable number). Controls: a deliberately wrong area (sigma alone) must vary."""
import json
from pathlib import Path

from mpmath import erf, exp, identify, mp, mpf, pi, sqrt

mp.dps = 25
DP = Path(__file__).parent / 'datos_pulsos'


def K_por_sigma():
    out = {}
    for b in sorted(d for d in DP.iterdir() if d.is_dir()):
        d = json.loads((b / f'defs_{b.name}.json').read_text())
        c = json.loads((b / f'conf_{b.name}.json').read_text())
        v = (c.get('hamiltonian') or {}).get('vars', {})
        if 'omegad0' not in v:
            continue
        dt = mpf(c['dt']) * (mpf(10) ** 9 if c['dt'] < 1e-6 else 1)
        for cmd in d.get('cmd_def', []):
            if cmd['name'] == 'x' and cmd['qubits'] == [0]:
                pp = [s for s in cmd['sequence'] if s.get('name') == 'parametric_pulse']
                if not pp:
                    continue
                p = pp[0]['parameters']
                a = p['amp']
                amp = abs(complex(*a)) if isinstance(a, list) else abs(mpf(a))
                sig, dur = int(p['sigma']), int(p['duration'])
                out.setdefault((sig, dur), []).append(mpf(v['omegad0']) * amp * sig * dt)
    return {k: sum(v) / len(v) for k, v in out.items()}


def lifted_disc(dur, s):
    c = mpf(dur) / 2
    g0 = exp(-((c + mpf(1) / 2) ** 2) / (2 * s ** 2))
    return sum((exp(-((t + mpf(1) / 2 - c) ** 2) / (2 * s ** 2)) - g0) / (1 - g0) for t in range(dur))


def plain_disc(dur, s, off=mpf(1) / 2):
    c = mpf(dur) / 2
    return sum(exp(-((t + off - c) ** 2) / (2 * s ** 2)) for t in range(dur))


def lifted_disc_int_t(dur, s):
    """lifted Gaussian sampled at integer t (Qiskit-old convention?), zero at t = -1 and t = dur"""
    c = mpf(dur) / 2
    g0 = exp(-((c + 1) ** 2) / (2 * s ** 2))
    return sum((exp(-((t - c) ** 2) / (2 * s ** 2)) - g0) / (1 - g0) for t in range(dur))


def lifted_cont(dur, s):
    c = mpf(dur) / 2
    g0 = exp(-(c ** 2) / (2 * s ** 2))
    return (s * sqrt(2 * pi) * erf(c / (sqrt(2) * s)) - dur * g0) / (1 - g0)


def lifted_gen(dur, s, off, cero):
    """Qiskit _lifted_gaussian: samples at t + off, zero at distance `cero` from the centre dur/2"""
    c = mpf(dur) / 2
    g0 = exp(-(cero ** 2) / (2 * s ** 2))
    return sum((exp(-((t + off - c) ** 2) / (2 * s ** 2)) - g0) / (1 - g0) for t in range(dur))


K = K_por_sigma()
for off in (0, mpf(1) / 2):
    for nom_cero, cero in (('c', lambda c: c), ('c+1/2', lambda c: c + mpf(1) / 2), ('c+1', lambda c: c + 1)):
        th = [K[k] * lifted_gen(k[1], mpf(k[0]), off, cero(mpf(k[1]) / 2)) / (k[0] * pi) for k in sorted(K)]
        v = [float(x) for x in th]
        print(f'lifted off={float(off)} cero={nom_cero:6s} theta/pi = {[round(x, 6) for x in v]}  rango {max(v) - min(v):.2e}')
print('K(sigma) = omegad*amp*sigma*dt:', {k: float(v) for k, v in sorted(K.items())})
CAND = {'lifted discreto (t+1/2)': lifted_disc, 'gauss discreto (t+1/2)': plain_disc,
        'gauss discreto (t)': lambda d, s: plain_disc(d, s, mpf(0)), 'lifted discreto (t)': lifted_disc_int_t,
        'lifted continuo': lifted_cont, 'gauss continuo infinito': lambda d, s: s * sqrt(2 * pi),
        'CONTROL sigma solo': lambda d, s: mpf(s)}
for nombre, A in CAND.items():
    th = {k: K[k] * A(k[1], mpf(k[0])) / (k[0] * pi) for k in sorted(K)}
    vals = [float(x) for x in th.values()]
    rango = max(vals) - min(vals)
    print(f'{nombre:26s} theta/pi = {[round(x, 6) for x in vals]}  rango {rango:.2e}'
          + (f'  identify: {identify(list(th.values())[1], ["pi", "sqrt(2)", "sqrt(pi)", "e"])}' if rango < 1e-3 else ''))
