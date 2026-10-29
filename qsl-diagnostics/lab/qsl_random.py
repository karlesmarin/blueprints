# encaje: los dados (🎲) de los laboratorios del blueprint qsl-diagnostics: cada random_* devuelve, como JSON, valores al azar DENTRO de los rangos que acepta su laboratorio y físicamente razonables para un transmón (29-oct-2026, Carles: «en laboratorio pon dado para que ponga valores al azar»)
"""Random inputs for the labs: each random_*() returns a JSON string {input: value} that its run_* accepts."""
import json
import math
import random

from qsl_data import SERIE


def _log_uniform(lo, hi):
    return math.exp(random.uniform(math.log(lo), math.log(hi)))


def random_fig1():
    """Figure 1: an anharmonicity of a real transmon and a drive fraction on the measured grid (log-uniform)."""
    return json.dumps({'delta_mhz': str(random.randint(200, 400)), 'r': '%.2f' % _log_uniform(0.1, 1.5)})


def random_fig2():
    """Figure 2: coupling, anharmonicity, CR drive fraction and qubit-qubit detuning of a plausible pair."""
    return json.dumps({'j': '%.4f' % random.uniform(0.004, 0.03), 'delta_mhz': str(random.randint(200, 400)),
                       'r': '%.2f' % random.uniform(0.1, 1.2), 'detuning_mhz': str(random.randint(40, 160))})


def random_fig4():
    """Figure 4: the law T_min ≈ max(π/Ω, ~1.1·2π/|δ|) for another anharmonicity and drive."""
    return json.dumps({'delta_mhz': str(random.randint(100, 600)), 'r': '%.2f' % _log_uniform(0.1, 1.5)})


def random_fig3():
    """Figure 3: a random view of the fleet in time: quantity, split, statistic, years and sometimes one backend out."""
    y0 = random.randint(2021, 2024)
    y1 = random.randint(y0 + 1, 2025)
    known = sorted({r[0] for r in SERIE})
    return json.dumps({'quantity': random.choice(['both', '1q', '2q']), 'split': random.choice(['none', 'gate', 'qubits']),
                       'statistic': random.choice(['median', 'mean']), 'from': str(y0), 'to': str(y1),
                       'exclude': random.choice(known) if random.random() < 0.3 else ''})


def random_bloch():
    """The Bloch-sphere lab: a random envelope (sometimes one drawn by hand), duration, area, DRAG and detuning."""
    shape = random.choice(['square', 'sine', 'gaussian', 'custom'])
    out = {'shape': shape, 'T': str(random.randint(5, 100)), 'area': '%.2f' % random.choice([0.5, 1, 1, 1.5, 2,
                                                                                              random.uniform(0.25, 2)]),
           'beta': '0' if random.random() < 0.5 else '%.1f' % random.uniform(-2, 2),
           'detuning_mhz': '0' if random.random() < 0.5 else '%.0f' % random.uniform(-30, 30),
           'samples': '0, 1, 3, 1, 0'}
    if shape == 'custom':
        k = random.randint(5, 9)
        out['samples'] = ', '.join('%.1f' % (0 if i in (0, k - 1) else random.uniform(0.2, 3)) for i in range(k))
    return json.dumps(out)


def random_device():
    """«Your device»: one plausible transmon pair (drive, anharmonicity, X time, coupling, two-qubit time)."""
    om = random.uniform(0.3, 1.5)                       # Omega_max, rad/ns
    tx = random.uniform(1.2, 12) * math.pi / om         # the X gate a few times above pi/Omega
    jq = random.uniform(0.005, 0.02)                    # rad/ns
    t2 = random.uniform(1.5, 8) * math.pi / (2 * jq)    # the two-qubit gate a few times above pi/(2 j_q)
    # 30-oct (Carles: «tengo la sensación de que se deja alguna»): e, eps and the list of gates also vary; a third of
    # the throws fill the list (the IBM processors, or a few gates of an invented device), which the lab diagnoses
    batch = ''
    if random.random() < 1 / 3:
        if random.random() < 0.5:
            batch = 'ibm'
        else:
            filas = []
            for k in range(random.randint(3, 6)):
                o = random.uniform(0.3, 1.5)
                j = random.uniform(0.005, 0.02)
                filas.append('q%d, %.3f, %.1f, %.4f, %.0f' % (k, o, random.uniform(0.8, 12) * math.pi / o, j,
                                                              random.uniform(0.8, 8) * math.pi / (2 * j)))
            batch = '\n'.join(filas)
    return json.dumps({'omega': '%.3f' % om, 'delta_mhz': str(random.randint(200, 380)), 'tx': '%.1f' % tx,
                       'e': '%.1e' % _log_uniform(1e-5, 1e-2), 'jq': '%.4f' % jq, 't2q': '%.0f' % t2,
                       'eps': '%.1e' % _log_uniform(1e-4, 1e-2), 'batch': batch})


def random_qudit():
    """The d-level CZ lab: a number of levels, a coupling and how far to draw."""
    d = random.randint(2, 10)
    return json.dumps({'d': str(d), 'j': '%.4f' % random.uniform(0.004, 0.03), 'dmax': str(random.randint(max(d + 4, 8), 30))})
