# encaje: figuras del borrador qsl-diagnostics (PDF vectorial para LaTeX) desde barrido.csv, pares.csv, serie.csv y el
# resultado de grape_1q.py; paleta categórica validada (dataviz, validate_palette.js: PASS); investigación.
"""Writes fig_1q_3d.pdf, fig_2q_3d.pdf, fig_ley_1q.pdf, fig_serie.pdf next to this script.
Colour carries identity only together with a marker shape (secondary encoding: two slots are < 3:1 on white)."""
import csv
from pathlib import Path

import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

AQUI = Path(__file__).parent
DATOS = AQUI.parent
PAL = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100']        # validated categorical slots 1-4 (fixed order)
MARC = ['o', 's', '^', 'D']
TINTA, TINTA2, REJILLA = '#1f1f1e', '#5c5b55', '#d9d8d2'
plt.rcParams.update({'font.size': 8, 'axes.edgecolor': TINTA2, 'axes.labelcolor': TINTA, 'xtick.color': TINTA2,
                     'ytick.color': TINTA2, 'axes.titlesize': 9, 'pdf.fonttype': 42, 'legend.frameon': False,
                     'lines.linewidth': 2})


def leer(nombre):
    with open(DATOS / nombre, encoding='utf-8') as f:
        return list(csv.DictReader(f))


def nuevo3d():
    """3D axes with a fixed draw order (computed_zorder=False: later series are drawn on top) and room for the
    vertical label (27-oct: the z label was clipped and the legend covered points)."""
    fig = plt.figure(figsize=(3.8, 3.3))
    ax = fig.add_axes([0.0, 0.12, 0.80, 0.86], projection='3d', computed_zorder=False)
    ax.zaxis.set_major_locator(matplotlib.ticker.MaxNLocator(5))
    return fig, ax


def leyenda_abajo(fig, ax):
    h, l = ax.get_legend_handles_labels()
    fig.legend(h, l, loc='lower center', ncol=len(l), fontsize=7, markerscale=1.8, handletextpad=0.2,
               columnspacing=0.8)


def estilo3d(ax):
    for eje in (ax.xaxis, ax.yaxis, ax.zaxis):
        eje.pane.set_facecolor('white')
        eje.pane.set_edgecolor(REJILLA)
        eje._axinfo['grid']['color'] = REJILLA
        eje._axinfo['grid']['linewidth'] = 0.5


# 1. single qubit, 3D: |delta|/2pi (MHz), omegad/2pi (MHz), tau_X / tau_QSL, by year
b = leer('barrido.csv')
fig, ax = nuevo3d()
años = sorted({r['fecha'][:4] for r in b})
for k, a in enumerate(años[:4]):
    rs = [r for r in b if r['fecha'][:4] == a]
    ax.scatter([abs(float(r['delta'])) / (2 * np.pi) * 1e3 for r in rs],
               [float(r['omegad']) / (2 * np.pi) * 1e3 for r in rs],
               [float(r['rx']) for r in rs], s=6, c=PAL[k], marker=MARC[k], depthshade=False, linewidths=0,
               label=f'{a} (n = {len(rs)})')
ax.set_xlabel(r'$|\delta|/2\pi$ (MHz)', labelpad=-2)
ax.set_ylabel(r'$\omega_d/2\pi$ (MHz)', labelpad=-2)
ax.set_zlabel(r'$\tau_X/\tau_{\rm QSL}$', labelpad=-1)
ax.tick_params(pad=-2)
estilo3d(ax)
ax.view_init(elev=18, azim=-58)
leyenda_abajo(fig, ax)
fig.savefig(AQUI / 'fig_1q_nube.pdf', bbox_inches='tight', pad_inches=0.08)   # superseded by figuras_3d.py
plt.close(fig)

# 2. two qubits, 3D: g/2pi (MHz), |Delta|/2pi (MHz), t / (pi / 2 jq), by gate type
p = leer('pares.csv')
fig, ax = nuevo3d()
ZMAX = 20      # z axis clipped; the pairs above are counted in the legend, never dropped silently
fuera_total = 0
for k, g in enumerate(['cx', 'ecr']):
    rs = [r for r in p if r['gate'] == g and r['det']]
    z = np.array([float(r['t']) / (np.pi / (2 * float(r['jq']))) for r in rs])
    dentro = z <= ZMAX
    fuera_total += int((~dentro).sum())
    ax.scatter(np.array([float(r['jq']) / (2 * np.pi) * 1e3 for r in rs])[dentro],
               np.array([abs(float(r['det'])) / (2 * np.pi) * 1e3 for r in rs])[dentro],
               z[dentro], s=6, c=PAL[k], marker=MARC[k], depthshade=False, linewidths=0,
               label=f'{g.upper()} (n = {len(rs)})')
ax.set_zlim(0, ZMAX)
ax.text2D(0.02, 0.97, f'{fuera_total} pairs above {ZMAX} not shown', transform=ax.transAxes, fontsize=6.5,
          color=TINTA2)
ax.set_xlabel(r'$g/2\pi$ (MHz)', labelpad=-2)
ax.set_ylabel(r'$|\Delta|/2\pi$ (MHz)', labelpad=-2)
ax.set_zlabel('')
ax.text2D(0.98, 0.97, r'vertical: $t_{2q}\,/\,(\pi/2J)$', transform=ax.transAxes, fontsize=7.5, color=TINTA,
          ha='right')   # 27-oct: the 3D z label of this panel was not drawn inside the figure
ax.tick_params(pad=-2)
estilo3d(ax)
ax.view_init(elev=18, azim=-58)
leyenda_abajo(fig, ax)
fig.savefig(AQUI / 'fig_2q_nube.pdf', bbox_inches='tight', pad_inches=0.08)   # superseded by figuras_3d.py
plt.close(fig)

# 3. optimal-control law (grape_1q.py, 4 levels, 1-F < 1e-4; values copied from RESULTADOS.md)
r = np.array([0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.5])
T = np.array([32.99, 16.49, 12.04, 8.17, 7.07, 6.91, 7.33])
fig, ax = plt.subplots(figsize=(3.5, 2.4))
rr = np.linspace(0.08, 1.6, 200)
ax.plot(rr, np.pi / rr, color=PAL[0], lw=1.5, ls='--', label=r'speed limit $\pi/\Omega_{\max}$')
ax.axhline(1.1 * 2 * np.pi, color=PAL[1], lw=1.5, ls=':', label=r'leakage branch (fit) $\approx 1.1\cdot 2\pi/|\delta|$')
ax.plot(r, T, color=TINTA, marker='o', ms=4, lw=1.2, label='shortest time found (4 levels)')
ax.axvline(0.09, color=TINTA2, lw=0.8)
ax.text(0.093, 3.2, 'IBM cap\n0.09', fontsize=7, color=TINTA2, va='bottom')
ax.set_xscale('log')
ax.set_yscale('log')
ax.set_xlabel(r'$\Omega_{\max}/|\delta|$')
ax.set_ylabel(r'$T_{\rm found}\,|\delta|$')
ax.grid(True, which='both', color=REJILLA, lw=0.4)
ax.legend(fontsize=7, loc='upper right')
fig.savefig(AQUI / 'fig_ley_1q.pdf', bbox_inches='tight')
plt.close(fig)

# 4. time series (serie.csv): per-year median of the per-snapshot medians, both gaps on one (dimensionless) axis
s = leer('serie.csv')
años = sorted({x['fecha'][:4] for x in s})
m1 = [np.median([float(x['rx_med']) for x in s if x['fecha'][:4] == a]) for a in años]
m2 = [np.median([float(x['r2_med']) for x in s if x['fecha'][:4] == a and x['r2_med']]) for a in años]
fig, ax = plt.subplots(figsize=(3.5, 2.2))
ax.plot(años, m1, color=PAL[0], marker='o', ms=5, label='single-qubit $X$')
ax.plot(años, m2, color=PAL[1], marker='s', ms=5, label='two-qubit CX/ECR')
for x, y in zip(años, m1):
    pass
ax.text(años[-1], m1[-1] + 0.4, f'{m1[-1]:.1f}', color=TINTA, fontsize=7, ha='center')
ax.text(años[-1], m2[-1] + 0.4, f'{m2[-1]:.1f}', color=TINTA, fontsize=7, ha='center')
ax.set_ylim(0, 13)
ax.set_ylabel('gate time / speed limit')
ax.grid(True, axis='y', color=REJILLA, lw=0.4)
ax.legend(fontsize=7, loc='center right')
fig.savefig(AQUI / 'fig_serie.pdf', bbox_inches='tight')
plt.close(fig)
print('figuras:', sorted(x.name for x in AQUI.glob('fig_*.pdf')))
