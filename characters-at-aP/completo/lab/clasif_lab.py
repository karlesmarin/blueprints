# encaje: laboratorio de characters-at-aP para el Teorema 5.1 (qué denominadores dan caracteres enteros): mapa (m, q) por familias
"""Lab of Theorem 5.1 (8-nov-2026): every character of Sp(2m) is an integer at g_{1/q} exactly when q | 2m, q | 2m+1,
q | 2m+2, or q = 6 with m ≡ 1 (mod 3). Two independent routes, as in the paper's proof:
  * the Galois route: all characters are integers iff the spectrum {±j mod q : 1 ≤ j ≤ m} of the natural
    representation is stable under ζ ↦ ζ^p for every p prime to q (computed directly, multiset by multiset);
  * the list of the theorem.
The map shows every point (m, q) of the box, coloured by the family that makes it integral; the lab reports any
point where the two routes disagree (there is none). Pure Python: it runs in the browser."""
import json
from collections import Counter
from math import gcd

import labkit as K

FAMILIAS = [('q | 2m', '#1B6F8C'), ('q | 2m+1', '#2E7D32'), ('q | 2m+2  (the powers of a_P)', '#B5530F'),
            ('q = 6, m ≡ 1 (mod 3)', '#6A1B9A')]


def espectro(m, q):
    c = Counter()
    for j in range(1, m + 1):
        c[j % q] += 1
        c[(-j) % q] += 1
    return c


def galois_estable(m, q):
    A = espectro(m, q)
    for p in range(2, q):
        if gcd(p, q) == 1:
            B = Counter()
            for r, n in A.items():
                B[(p * r) % q] += n
            if B != A:
                return False
    return True


def familia(m, q):
    if (2 * m) % q == 0:
        return 0
    if (2 * m + 1) % q == 0:
        return 1
    if (2 * m + 2) % q == 0:
        return 2
    if q == 6 and m % 3 == 1:
        return 3
    return None


def run_clasif(params):
    p = json.loads(params)
    try:
        M, Q, m0 = int(p.get('M', 15)), int(p.get('Q', 32)), int(p.get('m', 4))
    except ValueError:
        return K.error('the bounds and m must be integers')
    if not (2 <= M <= 40 and 2 <= Q <= 60):
        return K.error('choose 2 ≤ largest m ≤ 40 and 2 ≤ largest q ≤ 60')
    if not 2 <= m0 <= M:
        return K.error('the highlighted m must lie between 2 and the largest m')
    pts = [([], []) for _ in FAMILIAS]
    malos, total = [], 0
    for m in range(2, M + 1):
        for q in range(2, Q + 1):
            g, f = galois_estable(m, q), familia(m, q)
            if g != (f is not None):
                malos.append((m, q))
            if f is not None:
                total += 1
                pts[f][0].append(m)
                pts[f][1].append(q)
    series = [{'name': n, 'x': pts[i][0], 'y': pts[i][1], 'size': 3.4, 'color': c} for i, (n, c) in enumerate(FAMILIAS)]
    col = sorted(q for q in range(2, Q + 1) if familia(m0, q) is not None)
    series.append({'name': 'your m = %d' % m0, 'x': [m0] * len(col), 'y': col, 'size': 6, 'color': '#C62828'})
    # recuadro [0, múltiplo de 5]: marcas enteras en los ejes (8-nov)
    series.append({'name': '', 'x': [0, 5 * -(-M // 5)], 'y': [0, 5 * -(-Q // 5)], 'size': 0, 'color': '#ffffff'})
    fig = K.svg_plot(series, title='Sp(2m): the points g(1/q) where every character is an integer',
                     xlabel='m', ylabel='q', legend_below=True)
    t = 2 * m0 + 2
    txt = ('For \\(m = %d\\) (so \\(t = 2m+2 = %d\\)) every character of \\(\\mathrm{Sp}(%d)\\) is an integer at '
           '\\(g_{1/q}\\) for \\(q \\in \\{%s\\}\\) (with \\(q \\le %d\\)): the divisors of \\(2m = %d\\), of \\(2m+1 = %d\\) '
           'and of \\(2m+2 = %d\\)%s. In the box \\(2 \\le m \\le %d\\), \\(2 \\le q \\le %d\\): %d integral points. '
           'The Galois test on the spectrum and the list of Theorem 5.1 %s.'
           % (m0, t, 2 * m0, ', '.join(map(str, col)), Q, 2 * m0, 2 * m0 + 1, t,
              (', and the sporadic \\(q = 6\\)' if m0 % 3 == 1 and familia(m0, 6) == 3 else ''), M, Q, total,
              'agree at every point' if not malos else 'DISAGREE at %s' % malos[:5]))
    return K.result(txt, [fig])


def random_clasif():
    import random
    M = random.randint(8, 40)   # labcheck: el dado mueve todas las entradas (8-nov)
    return json.dumps({'M': str(M), 'Q': str(random.randint(12, 60)), 'm': str(random.randint(2, M))})


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    for args in ({'M': '40', 'Q': '60', 'm': '4'}, {'M': '15', 'Q': '32', 'm': '7'}):
        r = json.loads(run_clasif(json.dumps(args)))
        print(r.get('error') or r['text'][-200:])
    # control: una lista alterada (sin el esporádico) DEBE discrepar del test de Galois
    orig = familia
    familia = lambda m, q: None if q == 6 and m % 3 == 1 and (2 * m) % 6 and (2 * m + 1) % 6 and (2 * m + 2) % 6 else orig(m, q)
    r = json.loads(run_clasif(json.dumps({'M': '15', 'Q': '12', 'm': '4'})))
    print('control:', r['text'][-90:])
