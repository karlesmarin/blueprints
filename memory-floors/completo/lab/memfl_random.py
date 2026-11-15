# encaje: los dados (🎲) de los laboratorios de memory-floors: cada random_* devuelve, como JSON, valores al azar DENTRO de los
# rangos de su laboratorio y físicamente razonables (cada entrada cambia con el dado, como pide labcheck). Miré el catálogo
# (detector de teoremas, flavio): no generan entradas de laboratorio. No es herramienta de Excovery.
"""Random inputs for the labs of memory-floors; each random_*() returns a JSON string {input: value} that run_* accepts."""
import json
import math
import random


def _logu(lo, hi):
    return math.exp(random.uniform(math.log(lo), math.log(hi)))


def random_pstar():
    return json.dumps({'gq': '%.4f' % _logu(1e-3, 2.0), 'gm': '%.4f' % _logu(1e-3, 2.0)})


def random_cloud():
    T1q = _logu(8, 60)
    T1m = _logu(40, 400)
    return json.dumps({'T1q': '%.1f' % T1q, 'T2q': '%.1f' % (random.uniform(0.15, 1.0) * 2 * T1q),
                       'T1m': '%.1f' % T1m, 'T2m': '%.1f' % (random.uniform(0.15, 1.0) * 2 * T1m),
                       'n': str(random.randint(60, 250)), 'cap': random.choice(['1', '1', '1.5', '0.8', '%.2f' % random.uniform(0.6, 1.6)]),
                       'seed': str(random.randint(0, 9999))})


def random_fixed():
    return json.dumps({'phi': '%.3f' % random.uniform(0, 1.2), 'gq': '%.4f' % _logu(0.002, 0.1),
                       'gm': '%.5f' % _logu(0.0003, 0.05)})


def random_env():
    lo = random.uniform(1.52, 1.56)
    return json.dumps({'mode': str(random.randint(1, 3)), 'lo': '%.3f' % lo, 'hi': '%.3f' % (lo + random.uniform(0.02, 0.06))})


def random_rutgers():
    T1 = random.uniform(8, 120)
    return json.dumps({'T1q': '%.1f' % T1, 'T2q': '%.1f' % (T1 * random.uniform(0.4, 1.8)), 'mode': str(random.randint(1, 10))})


def random_surface():
    return json.dumps({'a': '%.2f' % random.uniform(0.7, 5), 'b': '%.2f' % _logu(0.7, 15), 'c': '%.1f' % _logu(1, 20)})


def random_cycle():
    return json.dumps({'mode': str(random.randint(1, 3)), 'scale': '%.2f' % _logu(0.05, 2.0), 't': '%.1f' % _logu(0.5, 150),
                       'delta': random.choice(['auto', '%.1f' % random.uniform(0, 60)])})


def random_strong():
    r = random.random()
    if r < 0.3:
        q = random.uniform(1.0, 6.0)
        return json.dumps({"phiq": "%.4f" % q, "phim": "%.4f" % q, "T": "auto"})
    if r < 0.65:
        return json.dumps({"phiq": "%.3f" % random.uniform(1.0, 9.0), "phim": "%.3f" % random.uniform(0.3, 9.0), "T": "auto"})
    m = _logu(0.3, 1.5)
    return json.dumps({"phiq": "%.3f" % (m + random.uniform(4.5, 12.0)), "phim": "%.3f" % m, "T": random.choice(["auto", "12", "40"])})


def random_unequal():
    D = random.uniform(2.1, 4.4)
    P = random.uniform(2.8, 4.8)
    m = (-D + math.sqrt(D * D + 4 * P)) / 2
    return json.dumps({"phiq": "%.4f" % (m + D), "phim": "%.4f" % m})
