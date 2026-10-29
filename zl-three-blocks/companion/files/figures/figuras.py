# Draws every figure of the paper (English and Spanish labels) from datos.py.
import re
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Polygon, Rectangle  # noqa: E402
from matplotlib.text import Text  # noqa: E402
from mpl_toolkits.mplot3d.art3d import Poly3DCollection  # noqa: E402

import datos  # noqa: E402
from rotulos_es import ES  # noqa: E402

OUT = Path(__file__).resolve().parents[1] / 'figs'
OUT.mkdir(exist_ok=True)
OK = ['#E69F00', '#56B4E9', '#009E73', '#F0E442', '#0072B2', '#D55E00', '#CC79A7', '#000000']
BLOQ = ['#E69F00', '#56B4E9', '#009E73']  # A, B, C
GRIS = '#4D4D4D'
plt.rcParams.update({'font.size': 9, 'font.family': 'serif', 'axes.spines.top': False, 'axes.spines.right': False})


def guardar(fig, nombre):
    """Guarda la figura en inglés y, con los rótulos de rotulos_es, su versión <nombre>_es; avisa de los rótulos con
    letras que no tienen traducción."""
    fig.savefig(OUT / f'{nombre}.pdf', bbox_inches='tight')
    fig.savefig(OUT / f'{nombre}.png', bbox_inches='tight', dpi=200)
    for t in fig.findobj(Text):
        s = t.get_text()
        if s in ES:
            t.set_text(ES[s])
        elif re.search(r'[a-zA-Z]{3,}', re.sub(r'\$[^$]*\$', '', s)):
            print(f'  [sin traducir en {nombre}] {s!r}')
    fig.savefig(OUT / f'{nombre}_es.pdf', bbox_inches='tight')
    fig.savefig(OUT / f'{nombre}_es.png', bbox_inches='tight', dpi=200)
    plt.close(fig)


def fig_cuadricula():
    """22×5 dibujada TRASPUESTA (las filas de la cuadrícula van en horizontal) para que ocupe el ancho de página;
    cada par lleva su número en sus dos celdas."""
    m, n, E1, E2, evita = datos.tres_bloques_22x5()
    fig, ax = plt.subplots(figsize=(7.4, 2.5))
    bl = [{0, 1}, {2, 3}, {4}]
    for j in range(n):
        b = next(i for i in range(3) if j in bl[i])
        ax.add_patch(Rectangle((-1.6, j - .5), .6, 1, color=BLOQ[b], lw=0))
        ax.text(-1.3, j, 'ABC'[b], fontsize=6.5, ha='center', va='center', color='white', weight='bold')
    for i in range(m):
        for j in range(n):
            ax.add_patch(Rectangle((i - .5, j - .5), 1, 1, fill=False, ec='#BBBBBB', lw=.4))
    for (i, j) in E1:
        ax.add_patch(Rectangle((i - .4, j - .4), .8, .8, color=GRIS))
    cmap = plt.get_cmap('tab20')
    sin_gris = [k for k in range(20) if k not in (14, 15)]  # tab20 14–15 son grises: se confunden con E1
    for k, ((i, j), (p, q)) in enumerate(E2):
        c = cmap(sin_gris[k % len(sin_gris)])
        ax.plot([i, p], [j, q], color=c, lw=.8, alpha=.8, zorder=1)
        for (a, b) in ((i, j), (p, q)):
            ax.add_patch(Rectangle((a - .4, b - .4), .8, .8, color=c, zorder=2))
            ax.text(a, b, str(k + 1), fontsize=4.6, ha='center', va='center', zorder=3)
    for i in range(m):
        ax.text(i, n - .15, 'ABC'[evita[i]], fontsize=6, ha='center', va='bottom', color=BLOQ[evita[i]])
    ax.text(m / 2 - .5, n + .55, 'block avoided by each row', fontsize=6.5, ha='center', color='#555555')
    ax.set_ylim(n + .9, -.7)
    ax.set_xlim(-1.8, m - .4)
    ax.set_xticks(range(m), [str(i + 1) for i in range(m)], fontsize=6)
    ax.set_yticks(range(n), [str(j + 1) for j in range(n)], fontsize=6)
    ax.set_xlabel('row $i$', fontsize=7)
    ax.set_ylabel('column $j$', fontsize=7)
    ax.set_aspect('equal')
    for s in ax.spines.values():
        s.set_visible(False)
    guardar(fig, 'fig1_three_blocks_22x5')


def fig_proyeccion():
    fig, ax = plt.subplots(figsize=(4.6, 3.2))
    V = {'A': (0, 0), 'B': (2, 0), 'C': (1, 1.6)}
    ax.add_patch(Polygon(list(V.values()), closed=True, fill=False, ls='--', ec='#999999'))
    for k, (nom, (x, y)) in enumerate(V.items()):
        ax.scatter([x], [y], s=380, color=BLOQ[k], zorder=3)
        ax.text(x, y, nom, ha='center', va='center', fontsize=11, color='white', weight='bold', zorder=4)
    lados = [('A', 'B', 'rows avoiding C', (1, -.2), 0), ('B', 'C', 'rows avoiding A', (1.83, 1.0), -58),
             ('A', 'C', 'rows avoiding B', (.17, 1.0), 58)]
    for k, (u, v, t, (tx, ty), rot) in enumerate(lados):
        (x1, y1), (x2, y2) = V[u], V[v]
        ax.plot([x1, x2], [y1, y2], color=OK[4 + k], lw=3, alpha=.7)
        ax.text(tx, ty, t, fontsize=7, ha='center', va='center', color=OK[4 + k], rotation=rot)
    # un par: extremo de una fila AC en el bloque A con uno de una fila BC en el bloque B; el bloque común es C
    import numpy as np
    th = np.linspace(np.radians(238), np.radians(302), 30)
    ax.plot(1 + .38 * np.cos(th), 1.6 + .38 * np.sin(th), color=OK[5], lw=1.6)
    fondo = dict(fc='white', ec='none', alpha=.9, pad=1)
    ax.text(1, 1.0, 'a pair: an angle at C\n(endpoints in A and B)', fontsize=6.5, ha='center', color=OK[5],
            bbox=fondo)
    ax.text(1, .42, 'face never filled:\nno row meets A, B, C', fontsize=6.5, ha='center', style='italic',
            color='#666666', bbox=fondo)
    for x in range(5):
        ax.scatter([-1.9 + .35 * x], [1.45], s=40, color=BLOQ[[0, 0, 1, 1, 2][x]])
    ax.text(-1.2, 1.62, 'columns', fontsize=7, ha='center')
    ax.annotate('', xy=(-.15, .9), xytext=(-1.1, 1.3), arrowprops=dict(arrowstyle='->', color='#777777'))
    ax.text(-.72, 1.0, 'projection', fontsize=7, color='#777777', rotation=-22, ha='center', va='top')
    ax.set_xlim(-2.2, 2.4)
    ax.set_ylim(-.35, 1.9)
    ax.axis('off')
    guardar(fig, 'fig2_projection_triangle')


def cubo(ax, x, y, z, color, alpha, ec='k'):
    v = [(x, y, z), (x + 1, y, z), (x + 1, y + 1, z), (x, y + 1, z),
         (x, y, z + 1), (x + 1, y, z + 1), (x + 1, y + 1, z + 1), (x, y + 1, z + 1)]
    caras = [[v[0], v[1], v[2], v[3]], [v[4], v[5], v[6], v[7]], [v[0], v[1], v[5], v[4]],
             [v[2], v[3], v[7], v[6]], [v[1], v[2], v[6], v[5]], [v[0], v[3], v[7], v[4]]]
    ax.add_collection3d(Poly3DCollection(caras, facecolors=color, edgecolors=ec, linewidths=.2, alpha=alpha))


def fig_tensor():
    """Izquierda: vista 3D. Derecha: las cinco rebanadas 3×3 (k = 1..5), planas, con cada celda visible:
    gris = base, número = par, × = vacía."""
    E1, P, U = datos.tensor_3x3x5()
    fig = plt.figure(figsize=(7.6, 3.0))
    ax = fig.add_axes([0.0, 0.0, 0.34, 1.0], projection='3d')
    for (x, y, z) in E1:
        cubo(ax, x, y, z, '#BBBBBB', .12, ec='#999999')
    for k, (a, b) in enumerate(P):
        for c in (a, b):
            cubo(ax, *c, OK[4 + k % 3] if k < 3 else OK[k], .85)
        ax.plot([a[0] + .5, b[0] + .5], [a[1] + .5, b[1] + .5], [a[2] + .5, b[2] + .5], color=OK[4 + k], lw=1.5)
    for c in U:
        ax.scatter([c[0] + .5], [c[1] + .5], [c[2] + .5], marker='x', color='k', s=30)
    ax.set_xlim(0, 3)
    ax.set_ylim(0, 3)
    ax.set_zlim(0, 5)
    ax.set_box_aspect((3, 3, 5))
    ax.set_xticks([.5, 1.5, 2.5], ['1', '2', '3'])
    ax.set_yticks([.5, 1.5, 2.5], ['1', '2', '3'])
    ax.set_zticks([.5, 1.5, 2.5, 3.5, 4.5], ['1', '2', '3', '4', '5'])
    ax.set_xlabel('$i$')
    ax.set_ylabel('$j$')
    ax.set_zlabel('$k$')
    ax.view_init(elev=22, azim=-58)
    color = {}
    for k, (a, b) in enumerate(P):
        color[a] = color[b] = (OK[4 + k], k + 1)
    E1s, Us = set(E1), set(U)
    for z in range(5):
        axs = fig.add_axes([0.37 + z * 0.127, 0.22, 0.115, 0.56])
        for x in range(3):
            for y in range(3):
                c = (x, y, z)
                fc = '#BBBBBB' if c in E1s else (color[c][0] if c in color else 'white')
                axs.add_patch(Rectangle((y, x), 1, 1, fc=fc, ec='#777777', lw=.6))
                if c in color:
                    axs.text(y + .5, x + .5, str(color[c][1]), ha='center', va='center', fontsize=8, color='white',
                             weight='bold')
                if c in Us:
                    axs.text(y + .5, x + .5, '$\\times$', ha='center', va='center', fontsize=9)
        axs.set_xlim(0, 3)
        axs.set_ylim(3, 0)
        axs.set_aspect('equal')
        axs.axis('off')
        axs.set_title(f'$k={z + 1}$', fontsize=8)
    fig.text(0.68, 0.1, 'rows $i$ downwards, columns $j$ to the right; grey: base; numbers: the three pairs; '
             '$\\times$: empty', ha='center', fontsize=6.5)
    guardar(fig, 'fig3_tensor_3x3x5')


def fig_pendientes():
    pts = datos.pendientes()
    fig, ax = plt.subplots(figsize=(4.4, 3.0))
    ns = [p[0] for p in pts]
    ax.plot(ns, [n / 3 for n in ns], color='#999999', ls=':', label='$n/3$ (density $1/3$, Lebedev)')
    ax.plot(ns, [float(p[1]) for p in pts], color=OK[4], lw=1, label='$\\lambda_n$ (three-block lower bound)')
    est = {'certificado': (OK[2], 'o', 'exact, certified'), 'calculado': (OK[0], 's', 'numerical optimum, not certified'),
           'cota inferior': (OK[4], '^', 'lower bound only')}
    vistos = set()
    for n, l, e in pts:
        c, mk, lab = est[e]
        ax.scatter([n], [float(l)], color=c, marker=mk, s=30, zorder=3, label=lab if e not in vistos else None)
        vistos.add(e)
        ax.annotate(f'{l}', (n, float(l)), textcoords='offset points', xytext=(4, -10), fontsize=6)
    ax.set_xlabel('number of columns $n$')
    ax.set_ylabel('slope $\\lim F_n(m)/m$')
    ax.legend(fontsize=6.5, frameon=False, loc='upper left')
    guardar(fig, 'fig4_slopes')


def fig_f4():
    v = datos.f4()
    fig, ax = plt.subplots(figsize=(4.6, 3.0))
    ms = list(v)
    ax.step(ms, [v[m] for m in ms], where='mid', color=GRIS, lw=1.2, label='$F_4(m)$, exact')
    a = [(2 * m - 3) // 3 for m in ms]
    b = [(3 * m - 12) // 4 for m in ms]
    ax.plot(ms, a, color=OK[5], lw=.8, ls='--', label='$\\lfloor(2m-3)/3\\rfloor$')
    ax.plot(ms, b, color=OK[4], lw=.8, ls='--', label='$\\lfloor(3m-12)/4\\rfloor$')
    ax.axvline(24, color='#BBBBBB', lw=.6)
    ax.text(24.3, 3, 'lines cross, $m=24$', fontsize=7, color='#777777')
    ax.set_xlabel('$m$')
    ax.set_ylabel('pairs')
    ax.legend(fontsize=7, frameon=False)
    guardar(fig, 'fig5_F4_staircase')


def fig_tabla():
    t = datos.tabla()
    ms = sorted({m for m, _ in t})
    ns = sorted({n for _, n in t})
    fig, ax = plt.subplots(figsize=(4.4, 4.6))
    col = {'publicado': '#D9D9D9', 'nuevo': OK[2], 'cota': OK[0]}
    for (m, n), (v, o, sup) in t.items():
        ax.add_patch(Rectangle((n - .5, m - .5), 1, 1, color=col[o], ec='white'))
        txt = str(v) if o != 'cota' else f'{v}–{sup}'
        ax.text(n, m, txt, ha='center', va='center', fontsize=6, color='k' if o != 'nuevo' else 'white')
    ax.set_xlim(min(ns) - .5, max(ns) + .5)
    ax.set_ylim(max(ms) + .5, min(ms) - .5)
    ax.set_xticks(ns)
    ax.set_yticks(ms)
    ax.set_xlabel('$n$')
    ax.set_ylabel('$m$')
    for k, lab in (('publicado', 'previously published'), ('nuevo', 'new exact value'), ('cota', 'bounds')):
        ax.add_patch(Rectangle((0, 0), 0, 0, color=col[k], label=lab))
    ax.legend(fontsize=6.5, frameon=False, loc='lower right')
    ax.set_title('$z_L(m,n)$: exact values and bounds', fontsize=8)
    guardar(fig, 'fig6_table')


def celda(ax, i, j, color, lw=0, ec=None, alpha=1):
    ax.add_patch(Rectangle((j - .4, i - .4), .8, .8, color=color, lw=lw, ec=ec, alpha=alpha))


def rejilla(ax, m, n):
    for i in range(m):
        for j in range(n):
            ax.add_patch(Rectangle((j - .5, i - .5), 1, 1, fill=False, ec='#CCCCCC', lw=.5))
    ax.set_xlim(-.6, n - .4)
    ax.set_ylim(m - .4, -.6)
    ax.set_aspect('equal')
    ax.axis('off')


def fig_definicion():
    fig, axs = plt.subplots(1, 3, figsize=(7.4, 2.7), gridspec_kw={'width_ratios': [1, 1, 1.25]})
    # (a) C2: un par no degenerado y sus dos celdas opuestas
    ax = axs[0]
    rejilla(ax, 4, 4)
    for c in ((0, 0), (2, 3)):
        celda(ax, *c, OK[5])
    ax.plot([0, 3], [0, 2], color=OK[5], lw=1)
    for c in ((0, 3), (2, 0)):
        ax.add_patch(Rectangle((c[1] - .4, c[0] - .4), .8, .8, fill=False, ec=OK[4], lw=1.6, ls='--'))
    ax.set_title('(a) C2: the opposite cells\n(dashed) are not both occupied', fontsize=7.5)
    # (b) C3: patrón prohibido de cinco celdas
    ax = axs[1]
    rejilla(ax, 4, 4)
    i, j, p, q, k, l = 0, 0, 2, 2, 3, 3
    for c in ((i, j), (p, q)):
        celda(ax, *c, OK[5])
    ax.plot([j, q], [i, p], color=OK[5], lw=1)
    for c in ((k, l), (k, j), (k, q), (i, l), (p, l)):
        celda(ax, *c, OK[6], alpha=.75)
    ax.set_title('(b) C3: these five cells (pink)\nare never all occupied', fontsize=7.5)
    # (c) ejemplo 4×3 en vista bipartita (como en la serie de Qi)
    ax = axs[2]
    E1 = [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1), (2, 2), (3, 0)]
    filas = [(0, 3 - r) for r in range(4)]
    cols = [(2, 2.5 - c) for c in range(3)]
    for (r, c) in E1:
        ax.plot([filas[r][0], cols[c][0]], [filas[r][1], cols[c][1]], color=GRIS, lw=1)
    for (r, c) in ((3, 1), (3, 2)):
        ax.plot([filas[r][0], cols[c][0]], [filas[r][1], cols[c][1]], color=OK[5], lw=1.4, ls='--')
    for r, (x, y) in enumerate(filas):
        ax.scatter([x], [y], s=120, color='white', ec='k', zorder=3)
        ax.text(x - .25, y, f'$x_{r + 1}$', ha='right', va='center', fontsize=8)
    for c, (x, y) in enumerate(cols):
        ax.scatter([x], [y], s=120, color='white', ec='k', zorder=3)
        ax.text(x + .25, y, f'$y_{c + 1}$', ha='left', va='center', fontsize=8)
    ax.set_xlim(-.8, 2.8)
    ax.set_ylim(-.5, 3.5)
    ax.axis('off')
    ax.set_title('(c) $z_L(4,3)=8$: seven 1-edges (solid)\nand one pair (dashed)', fontsize=7.5)
    guardar(fig, 'fig0_definition')


def fig_plantilla():
    """Plantilla de tres bloques en anchura fija: filas agrupadas por tipo, columnas por bloque."""
    fig, ax = plt.subplots(figsize=(4.4, 3.6))
    cb = [(0, 2), (2, 4), (4, 5)]  # columnas de A, B, C (proporcional)
    grupos = [('rows of type AB\n(avoid C)', (0, 1), 0), ('rows of type AC\n(avoid B)', (0, 2), 1),
              ('rows of type BC\n(avoid A)', (1, 2), 2)]
    y = 0
    altos = [1.2, 1.6, 1.6]
    for (nom, tipo, k), h in zip(grupos, altos):
        for b in range(3):
            x0, x1 = cb[b]
            ocupado = b in tipo
            ax.add_patch(Rectangle((x0, y), x1 - x0, h, color=BLOQ[b] if ocupado else 'white', alpha=.55 if ocupado else 1,
                                   ec='#777777', lw=.6))
            if not ocupado:
                ax.text((x0 + x1) / 2, y + h / 2, 'empty', ha='center', va='center', fontsize=6.5, style='italic',
                        color='#777777')
        ax.text(-.15, y + h / 2, nom, ha='right', va='center', fontsize=7)
        y += h
    for b, nom in enumerate('ABC'):
        ax.text((cb[b][0] + cb[b][1]) / 2, -.2, f'block\n{nom}', ha='center', fontsize=7.5, color=BLOQ[b], weight='bold')
    # canales: AB en A <-> BC en C (común B), etc.
    ax.annotate('', xy=(4.5, 3.7), xytext=(1.0, .6), arrowprops=dict(arrowstyle='<->', color=OK[5], lw=1.1))
    ax.text(5.2, 2.2, 'a channel:\nAB-rows in A\n$\\leftrightarrow$ BC-rows in C\n(common block B)', fontsize=6.5,
            color=OK[5], ha='left', va='center')
    ax.set_xlim(-2.4, 7.0)
    ax.set_ylim(y + .1, -.45)
    ax.axis('off')
    guardar(fig, 'fig_template_blocks')


def fig_mapa():
    """Mapa del artículo: resultados como cajas, dependencias como flechas, color = en qué se apoya."""
    from matplotlib.patches import FancyBboxPatch
    base = {'prueba': ('#FFFFFF', '#333333', 'proof in the text'), 'lean': (OK[2], 'white', 'proof + formal (Lean/Isabelle)'),
            'cert': (OK[4], 'white', 'certified computation'), 'calc': (OK[0], 'black', 'exhaustive computer search'),
            'evid': ('#F3DDB5', 'black', 'numerical evidence only'),
            'abierto': ('#EEEEEE', '#777777', 'open question')}
    nodos = {
        'def': (0.0, 4.2, 'Definition\n(C2), (C3)', 'prueba'),
        'zmn': (2.7, 4.2, '$z(m,n)=m+\\binom{n}{2}$\n(Čulík)', 'prueba'),
        'somb': (8.1, 4.2, 'shadows of triples\n+ dual certificates', 'cert'),
        'rect': (0.0, 2.8, 'each pair forces an\nempty rectangle', 'prueba'),
        'vert': (2.7, 2.8, 'Lemma:\nvertical pairs', 'lean'),
        'blq': (5.4, 2.8, 'Lemma: blocks\n(hollow triangle)', 'lean'),
        '3d': (0.0, 1.4, 'one dimension more\n$3\\times3\\times5$', 'calc'),
        'full': (2.7, 1.4, 'Lemma: one full\nrow (any $n$)', 'lean'),
        'mod': (5.4, 1.4, 'modules\n$\\Rightarrow\\ \\lambda_n$ lower bound', 'prueba'),
        'B': (8.1, 1.4, 'Theorem B\n$\\rho_n=\\lambda_n$, $n\\leq 6$', 'cert'),
        'rho': (10.6, 2.8, 'Theorem C\n$\\rho_n$ exists, rational', 'prueba'),
        'A': (2.7, 0.0, 'Theorem A\n$z_L(m,3)$', 'lean'),
        'wk': (0.0, 0.0, 'Corollary\nweak gap $m/6$', 'prueba'),
        'tab': (5.4, 0.0, 'exact values\n(small grids)', 'calc'),
        'f4': (8.1, 2.8, 'Theorem E: $F_4(m)$\nfor $m\\geq 6$', 'cert'),
        'n7': (8.1, 0.0, '$n=7$: $9/5$', 'evid'),
        'q': (10.6, 0.7, 'conjecture:\n$\\rho_n=\\lambda_n$\nfor all $n$', 'abierto'),
        'fam': (5.4, 4.2, 'Prop.: balanced blocks\noptimal in the family', 'prueba'),
        'can': (13.1, 4.2, 'Theorem D\ncanonical slope $\\kappa_n$', 'prueba'),
        'gap': (13.1, 1.4, 'Corollary: linear\ngap to $z_{RL}$, $z_2$', 'prueba'),
        'per': (13.1, 2.8, 'Theorem F: eventual\nperiodicity (any $n$)', 'prueba'),
    }
    aristas = [('def', 'rect'), ('def', 'zmn'), ('zmn', 'vert'), ('rect', 'vert'), ('vert', 'full'), ('full', 'A'),
               ('vert', 'blq'), ('blq', 'mod'), ('mod', 'B'), ('somb', 'rho'), ('rho', 'B'), ('zmn', 'somb'),
               ('rect', '3d'), ('A', 'wk'), ('B', 'n7'), ('n7', 'q'), ('rho', 'q'), ('mod', 'tab'), ('somb', 'f4'),
               ('blq', 'fam'), ('somb', 'can'), ('rho', 'gap'), ('rho', 'per')]
    fig, ax = plt.subplots(figsize=(9.2, 4.4))
    W, H = 2.25, 0.8

    def borde(x1, y1, x2, y2):
        """Punto donde el segmento desde el centro (x1, y1) hacia (x2, y2) sale de la caja W × H."""
        dx, dy = x2 - x1, y2 - y1
        t = min((W / 2) / abs(dx) if dx else 9e9, (H / 2) / abs(dy) if dy else 9e9)
        return x1 + t * dx, y1 + t * dy
    for a, b in aristas:
        (x1, y1), (x2, y2) = nodos[a][:2], nodos[b][:2]
        if (a, b) == ('zmn', 'somb'):  # por encima de la caja de la Proposición, que está en medio de la fila
            ax.annotate('', xy=(x2 - .3, y2 + H / 2), xytext=(x1 + .3, y1 + H / 2),
                        arrowprops=dict(arrowstyle='->', color='#777777', lw=.9, shrinkA=1, shrinkB=1,
                                        connectionstyle='arc3,rad=-0.18'))
            continue
        ax.annotate('', xy=borde(x2, y2, x1, y1), xytext=borde(x1, y1, x2, y2),
                    arrowprops=dict(arrowstyle='->', color='#777777', lw=.9, shrinkA=1, shrinkB=1))
    for k, (x, y, txt, tipo) in nodos.items():
        fc, tc, _ = base[tipo]
        ax.add_patch(FancyBboxPatch((x - W / 2, y - H / 2), W, H, boxstyle='round,pad=0.02,rounding_size=0.12',
                                    fc=fc, ec='#555555', lw=.8, zorder=3))
        ax.text(x, y, txt, ha='center', va='center', fontsize=6.2, color=tc, zorder=4,
                weight='bold' if k in ('A', 'B', 'rho', 'f4', 'can', 'per') else 'normal')
    # leyenda: cada etiqueta empieza tras su cuadrado y la siguiente entrada empieza tras el texto (sin solapes)
    pos = [(-1.0, -0.95), (4.0, -0.95), (9.0, -0.95), (-1.0, -1.35), (4.0, -1.35), (9.0, -1.35)]
    for (x0, y0), (tipo, (fc, tc, lab)) in zip(pos, base.items()):
        ax.add_patch(FancyBboxPatch((x0, y0 - .11), .3, .22, boxstyle='round,pad=0.01', fc=fc, ec='#555555'))
        ax.text(x0 + .42, y0, lab, fontsize=6.3, va='center')
    ax.set_xlim(-1.3, 14.4)
    ax.set_ylim(-1.55, 5.45)
    ax.axis('off')
    guardar(fig, 'fig_map')


if __name__ == '__main__':
    for f in (fig_mapa, fig_definicion, fig_plantilla, fig_cuadricula, fig_proyeccion, fig_tensor, fig_pendientes, fig_f4,
              fig_tabla):
        f()
        print('ok', f.__name__, flush=True)
