# encaje: figuras del laboratorio de characters-at-aP (cajas de capacidad de la Prop. 6.2, mapa de supervivientes de la Fig. 4)
"""Two figures for the lab of characters-at-aP, pure Python (Pyodide):

- ``boxes(classes, q, d)``: the folded residue classes modulo q as columns of boxes, as many as the capacity (d, or
  ⌊d/2⌋ on a fixed class); the entries ℓ_i fill them. A class over capacity shows its extra entries in red: that is
  Corollary 6.1. This is Figure 2 of the paper (Proposition 6.2) for the reader's own weight.
- ``survivors_map(...)`` in aP_value: the weights around λ, coloured by sign and sized by |χ| (Figures 3 and 4)."""
import labkit as K


def boxes(classes, q, d, title=''):
    cols = list(range(q // 2 + 1))
    caps = [(d // 2) if (2 * c) % q == 0 else d for c in cols]
    occ = [sorted(classes.get(c, []), reverse=True) for c in cols]
    hmax = max(max(caps), max(len(o) for o in occ), 1)
    W, H, top = 46, 26, 34
    inner = W * len(cols) + 8 * (len(cols) - 1)
    # 8-nov: ancho mínimo 560 y contenido centrado; con un viewBox estrecho el navegador la ampliaba a toda la página
    vw = max(560, inner + 24)
    left = (vw - inner) // 2
    height = top + H * hmax + 46
    o = ['<svg viewBox="0 0 %d %d" style="width:100%%;max-width:%dpx;background:#fff" xmlns="http://www.w3.org/2000/svg">'
         % (vw, height, vw),
         '<text x="%d" y="18" font-size="13" text-anchor="middle">%s</text>' % (vw // 2, K.esc(title))]
    base = top + H * hmax
    for i, c in enumerate(cols):
        x = left + i * (W + 8)
        for j in range(max(caps[i], len(occ[i]))):
            y = base - (j + 1) * H
            inside = j < caps[i]
            filled = j < len(occ[i])
            fill = ('#1B6F8C' if inside else '#C62828') if filled else '#fff'
            dash = '' if inside else ' stroke-dasharray="3 2"'
            o.append('<rect x="%d" y="%d" width="%d" height="%d" fill="%s" fill-opacity="%s" stroke="#555"%s/>'
                     % (x, y, W, H - 3, fill, '0.85' if filled else '1', dash))
            if filled:
                o.append('<text x="%d" y="%d" font-size="12" text-anchor="middle" fill="#fff">%d</text>'
                         % (x + W // 2, y + H // 2 + 2, occ[i][j]))
        fixed = (2 * c) % q == 0
        o.append('<text x="%d" y="%d" font-size="12" text-anchor="middle">%s%s</text>'
                 % (x + W // 2, base + 16, ('±%d' % c) if c and not fixed else str(c), '*' if fixed else ''))
        o.append('<text x="%d" y="%d" font-size="10" text-anchor="middle" fill="#555">cap %d</text>'
                 % (x + W // 2, base + 30, caps[i]))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': ''}
