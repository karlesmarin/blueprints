# encaje: lab del blueprint bsr-width-three: el Corolario 7 frente a las cotas superiores conocidas de BSR(m,n)
"""Upper bounds for BSR(m,n): the covering bound mn − max(m,n) + 1 [BSSV, Cor. 2.15], the bound of [BSSV, Thm 2.1]
(the largest p with p(p+1)/2 < C(m+1,2)·C(n+1,2)) and, for m, n ≥ 3, the bound mn − max(m,n) proved with Theorem 1
(Corollary 7 states it in width four, where it is new). Checked in Curiosity by analisis/cor7_comparar_cotas.py."""
import json
from math import comb

import labkit as K


def bssv(m, n):
    D = comb(m + 1, 2) * comb(n + 1, 2)
    p = 0
    while (p + 1) * (p + 2) // 2 < D:
        p += 1
    return p


def cotas(m, n):
    cub = m * n - max(m, n) + 1
    c7 = m * n - max(m, n) if min(m, n) >= 3 else None
    return cub, bssv(m, n), c7


def run_cotas(params):
    p = json.loads(params) if isinstance(params, str) else params
    try:
        m, n = int(p.get('m', 4)), int(p.get('n', 4))
    except ValueError:
        return K.error('m and n must be whole numbers')
    if not (3 <= m <= 40 and 3 <= n <= 8):
        return K.error('choose 3 ≤ m ≤ 40 and 3 ≤ n ≤ 8')
    cub, b21, c7 = cotas(m, n)
    antes = min(cub, b21)
    if c7 < antes:
        veredicto = 'the bound with Theorem 1, %d, is below both previous bounds (best before: %d)' % (c7, antes)
    elif c7 == antes:
        veredicto = 'the bound with Theorem 1, %d, only equals the best previous bound' % c7
    else:
        veredicto = 'the bound with Theorem 1, %d, is worse than [BSSV, Theorem 2.1], which gives %d' % (c7, b21)
    extra = ''
    if min(m, n) == 3:
        extra = ' Here min(m, n) = 3, so this is the exact value 2·max(m, n) of Theorem 1.'
    elif (m, n) == (4, 4):
        extra = ' With the lower bound 11 of Qi and Cui: 11 ≤ BSR(4,4) ≤ 12.'
    # 8-nov (V245: con (4,5) decía «para n ≥ 5 BSSV es igual o mejor» y la tabla mostraba 15 < 16): la frase general
    # depende de min(m, n), como en el paper, y la del caso sale de los mismos valores que la tabla (arriba)
    s = min(m, n)
    general = ('Here min(m, n) = 4: the case of Corollary 7 (exchanging x and y if needed), where the bound is new.'
               if s == 4 else
               'Here min(m, n) = %d ≥ 5: there [BSSV, Theorem 2.1] is never worse than mn − max(m, n) (the identity '
               'after Corollary 7).' % s if s >= 5 else '')
    txt = ('m = %d, n = %d: covering bound %d, [BSSV, Theorem 2.1] %d; %s.%s %s'
           % (m, n, cub, b21, veredicto, extra, general))
    ms = list(range(3, 31))
    serie = lambda k, nombre, color, modo: {'name': nombre, 'x': ms, 'y': [cotas(x, n)[k] - x * n for x in ms],
                                           'mode': modo, 'color': color}
    fig = K.svg_plot([serie(0, 'covering bound', '#888888', 'line'), serie(1, '[BSSV, Thm 2.1]', '#1B6F8C', 'line'),
                      serie(2, 'with Theorem 1 (mn − max)', '#B5530F', 'points'),
                      {'name': 'your m', 'x': [m], 'y': [c7 - m * n], 'mode': 'points', 'color': '#000000', 'size': 9}],
                     title='upper bounds minus mn, width n = %d (lower is better)' % n, xlabel='m',
                     ylabel='bound − mn', legend_below=True)
    filas = [[x, cotas(x, n)[0], cotas(x, n)[1], cotas(x, n)[2]] for x in sorted({3, 4, 5, 6, 8, 10, 20, m})]
    return K.result(txt, [fig], K.table(['m', 'covering', 'BSSV Thm 2.1', 'with Theorem 1'], filas))


def random_cotas():
    import random
    return json.dumps({'m': str(random.randint(3, 30)), 'n': str(random.randint(3, 7))})
