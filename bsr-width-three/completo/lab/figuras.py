# encaje: figuras SVG propias del blueprint bsr-width-three (matrices como mapas de color); Python puro, Pyodide
"""matrices_svg: the matrix C = [I P Q] of Lemma 2 drawn cell by cell, next to the diagonal of PQ − QP, which is the
reason the lemma works (invertible ⇒ M = 0); the control Q = P draws the same with a zero diagonal."""
import labkit as K

PAL = ['#ffffff', '#cfe3ea', '#8fc1d1', '#4f9bb5', '#1B6F8C', '#0f4a5f']
NEG = ['#ffffff', '#f3d9c9', '#e6ab88', '#d27c4c', '#B5530F', '#7d3808']


def _col(v, vmax):
    if v == 0:
        return '#ffffff'
    k = min(5, 1 + int(4 * abs(v) / max(vmax, 1)))
    return (PAL if v > 0 else NEG)[k]


def _block(o, M, x0, y0, c, vmax, etiqueta):
    for r, fila in enumerate(M):
        for j, v in enumerate(fila):
            o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s" stroke="#ddd"/>'
                     % (x0 + j * c, y0 + r * c, c, c, _col(v, vmax)))
            if v and c >= 14:
                o.append('<text x="%.1f" y="%.1f" font-size="%d" text-anchor="middle" fill="%s">%d</text>'
                         % (x0 + (j + .5) * c, y0 + (r + .7) * c, int(c * .55), '#fff' if abs(v) > vmax / 2 else '#222', v))
    o.append('<text x="%.1f" y="%.1f" font-size="12" text-anchor="middle">%s</text>'
             % (x0 + len(M[0]) * c / 2, y0 - 6, K.esc(etiqueta)))


def matrices_svg(P, Q, title):
    m = len(P)
    c = max(8, min(26, 300 // (3 * m)))
    PQ = [[sum(P[i][k] * Q[k][j] for k in range(m)) for j in range(m)] for i in range(m)]
    QP = [[sum(Q[i][k] * P[k][j] for k in range(m)) for j in range(m)] for i in range(m)]
    diag = [[PQ[i][i] - QP[i][i]] for i in range(m)]
    I = [[int(i == j) for j in range(m)] for i in range(m)]
    vmax = max(max(abs(v) for f in Q for v in f), max(abs(d[0]) for d in diag), 1)
    W = 3 * m * c + 4 * c + 120
    H = m * c + 90
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (W, H),
         '<text x="%d" y="16" font-size="13" text-anchor="middle">%s</text>' % (W / 2, K.esc(title))]
    y0 = 44
    for b, (M, et) in enumerate(((I, 'I'), (P, 'P'), (Q, 'Q'))):
        _block(o, M, 20 + b * (m * c + 8), y0, c, vmax, et)
    xd = 20 + 3 * (m * c + 8) + 40
    _block(o, diag, xd, y0, c, vmax, 'diag(PQ − QP)')
    inv = all(d[0] != 0 for d in diag) and all(PQ[i][j] - QP[i][j] == 0 for i in range(m) for j in range(m) if i != j)
    nota = ('PQ − QP is diagonal with no zero entry: invertible, so M(PQ − QP) = 0 forces M = 0' if inv else
            'PQ − QP = 0: the argument gives nothing and Hankel multipliers survive')
    o.append('<text x="%d" y="%d" font-size="11" text-anchor="middle" fill="%s">%s</text>'
             % (W / 2, H - 12, '#1B6F8C' if inv else '#B5530F', K.esc(nota)))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': title}
