# encaje: identifica la constante 1,148 de pulsos_x.py (omegad * amp * área / pi, igual en 32 backends) con mpmath.identify;
# investigación, no herramienta.
"""For the calibrated x pulse, theta = omegad * |amp| * area(lifted Gaussian) * dt is 1.148*pi on every backend.
Compute the ratio with high precision for (duration, sigma) = (160, 40) and (96, 24), compare with the plain
(untruncated) Gaussian area sigma*sqrt(2*pi) and other candidate normalisations, and try mpmath.identify."""
import json
from pathlib import Path

from mpmath import erf, exp, identify, mp, mpf, pi, sqrt

mp.dps = 30
RAIZ = (Path(__file__).parent / 'datos_pulsos')   # qiskit-terra 0.24.1 defs/conf (Apache 2.0)


def lifted_area(dur, sigma):
    c = mpf(dur) / 2
    g0 = exp(-((mpf(-1) - c + 1) ** 2) / (2 * sigma ** 2))
    return sum((exp(-((mpf(t) + mpf(1) / 2 - c) ** 2) / (2 * sigma ** 2)) - g0) / (1 - g0) for t in range(dur))


for nombre in ['athens', 'cairo', 'armonk']:
    d = json.loads((RAIZ / nombre / f'defs_{nombre}.json').read_text())
    c = json.loads((RAIZ / nombre / f'conf_{nombre}.json').read_text())
    om = mpf(c['hamiltonian']['vars']['omegad0'])
    x = [cmd for cmd in d['cmd_def'] if cmd['name'] == 'x' and cmd['qubits'] == [0]][0]
    p = [s for s in x['sequence'] if s.get('name') == 'parametric_pulse'][0]['parameters']
    amp = abs(complex(*p['amp'])) if isinstance(p['amp'], list) else abs(mpf(p['amp']))
    dur, sig = p['duration'], mpf(p['sigma'])
    dt = mpf(c['dt']) * (mpf(10) ** 9 if c['dt'] < 1e-6 else 1)
    la, pa = lifted_area(dur, sig), sig * sqrt(2 * pi)
    th = om * amp * la * dt
    print(f'{nombre}: dur={dur} sigma={sig} amp={amp:.6f} omegad={om} dt={dt}')
    print(f'   theta/pi (lifted)   = {th / pi}')
    print(f'   theta/pi (plain)    = {om * amp * pa * dt / pi}')
    print(f'   lifted/plain area   = {la / pa}   erf(dur/(2 sqrt2 sigma)) = {erf(dur / (2 * sqrt(2) * sig))}')
    print(f'   identify(theta/pi)  = {identify(th / pi, ["pi", "sqrt(2)", "sqrt(pi)", "e"])}')
    print(f'   omegad*dt*amp*sigma = {om * dt * amp * sig}   (x sqrt(2 pi) = {om * dt * amp * pa})')
