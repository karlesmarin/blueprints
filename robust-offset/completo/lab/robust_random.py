# encaje: los dados (🎲) de los laboratorios del blueprint robust-offset; cada random_* devuelve JSON con valores al azar
# DENTRO de los rangos que acepta su laboratorio (como qsl_random.py de qsl-diagnostics; lo comprueba lemmario labcheck).
# Catálogo mirado (labweb, lemmario, certificado racional LP): ninguna genera entradas aleatorias de estos laboratorios.
"""Random inputs for the labs: each random_*() returns a JSON string {input: value} that its run_* accepts."""
import json
import math
import random


def _log_uniform(lo, hi):
    return math.exp(random.uniform(math.log(lo), math.log(hi)))


def random_disk():
    kind = random.choice(['bangbang', 'twt', 'back', 'random', 'random'])
    a = {'bangbang': random.uniform(-math.pi / 2, math.pi / 2), 'twt': random.uniform(0.1, math.pi - 0.1),
         'back': random.uniform(0.1, math.pi / 2 - 0.05), 'random': random.uniform(0.1, 1.5)}[kind]
    return json.dumps({'pulse': kind, 'a': '%.3f' % a, 'w': '%.2f' % random.uniform(0, 3), 'seed': str(random.randint(1, 999)),
                       'k': str(random.randint(2, 9)), 'umax': random.choice(['1', '1', '1', '1.5', '2.5']),
                       'dmax': random.choice(['0', '1', '2', '3'])})


def random_cost():
    return json.dumps({'gq': '%.4g' % _log_uniform(1e-3, 1.0), 'gm': '%.4g' % _log_uniform(1e-3, 1.0)})


def random_second():
    return json.dumps({'rho': '%.3f' % random.uniform(0, 0.3), 'd': '%.3f' % random.uniform(0.05, 1.4),
                       'lam': '%.2f' % _log_uniform(1, 1000)})


def random_corr():
    return json.dumps({'kappa': '%.2f' % random.uniform(0, 1), 'rho': '%.4f' % _log_uniform(0.005, 3)})


def random_unified():
    z = lambda: random.choice(['0', '%.4g' % _log_uniform(1e-3, 10)])
    sm = z()
    kap = '0' if float(sm) == 0 else random.choice(['0', '%.2f' % random.uniform(0, 1)])
    return json.dumps({'sq': '%.4g' % _log_uniform(0.01, 10), 'sm': sm, 'kappa': kap,
                       'gq': z(), 'gm': z(), 'G': random.choice(['0.5', '1', '%.3f' % _log_uniform(0.2, 3)]),
                       'd': '%.3f' % random.uniform(0, math.pi / 2)})


def random_relax():
    return json.dumps({'r': random.choice(['0', '%.2f' % _log_uniform(0.1, 1000)]), 'lam': '%.2f' % _log_uniform(2, 150)})
