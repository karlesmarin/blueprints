# encaje: figuras 3D «superficie física + chips de IBM encima» del borrador qsl-diagnostics (sustituyen a las nubes de
# puntos de figuras.py, que no se entendían); datos de datos_pulsos/ (qiskit-terra 0.24.1, Apache 2.0); investigación.
"""fig_1q_3d.pdf: surface = minimum X-gate time with optimal control (law measured by grape_1q.py: T|delta| as a
function of r = Omega_max/|delta|, interpolated in log-log) over (|delta|/2pi, r); one point per IBM processor at its
median (|delta|, r = Omega_peak/|delta|, tau_X) with a vertical drop line to the surface = time above the physical
minimum at the same drive fraction.
fig_2q_3d.pdf: surface = CNOT time allowed by first-order cross resonance, t = (pi/2)/nu, nu = J r |dc/(dc + Delta)|,
over (r = Omega_CR/Delta, Delta/2pi) at the median J and delta; floor plane = exchange speed limit pi/(2J); one point
per processor at its median (r, Delta, CX duration) with a drop line to the surface."""
import json
from pathlib import Path

import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from matplotlib import cm  # noqa: E402

AQUI = Path(__file__).parent
DP = AQUI.parent / 'datos_pulsos'
AZUL, NARANJA, TINTA, TINTA2, REJILLA = '#2a78d6', '#eb6834', '#1f1f1e', '#5c5b55', '#d9d8d2'
plt.rcParams.update({'font.size': 8, 'pdf.fonttype': 42, 'axes.labelcolor': TINTA, 'xtick.color': TINTA2,
                     'ytick.color': TINTA2})
DOS_PI = 2 * np.pi


def amp_abs(a):
    return abs(complex(*a)) if isinstance(a, list) else abs(a)


def lifted_area(dur, sigma, width=0):
    t = np.arange(dur) + 0.5
    if width:
        rf = (dur - width) / 2
        g = np.where(t < rf, np.exp(-((t - rf) ** 2) / (2 * sigma ** 2)),
                     np.where(t > rf + width, np.exp(-((t - rf - width) ** 2) / (2 * sigma ** 2)), 1.0))
        g0 = np.exp(-((rf + 0.5) ** 2) / (2 * sigma ** 2))
    else:
        c = dur / 2
        g = np.exp(-((t - c) ** 2) / (2 * sigma ** 2))
        g0 = np.exp(-((c + 0.5) ** 2) / (2 * sigma ** 2))
    return float(np.sum((g - g0) / (1 - g0)))


def chips():
    """Per backend: medians of (|delta| rad/ns, r_1q, tau_X ns) and of (r_CR, |Delta| rad/ns, CX ns, J)."""
    out = []
    for b in sorted(d for d in DP.iterdir() if d.is_dir()):
        d = json.loads((b / f'defs_{b.name}.json').read_text())
        c = json.loads((b / f'conf_{b.name}.json').read_text())
        v = (c.get('hamiltonian') or {}).get('vars', {})
        if 'omegad0' not in v:
            continue
        dt = c['dt'] * (1e9 if c['dt'] < 1e-6 else 1)
        ctrl = {int(n[1:]): info['operates']['qubits'][0] for n, info in (c.get('channels') or {}).items()
                if n.startswith('u') and info.get('operates', {}).get('qubits')}
        ulo = c.get('u_channel_lo', [])
        uno, dos = [], []
        for cmd in d.get('cmd_def', []):
            pp = [s for s in cmd['sequence'] if s.get('name') == 'parametric_pulse']
            if cmd['name'] == 'x' and len(cmd['qubits']) == 1 and pp:
                q = cmd['qubits'][0]
                if v.get(f'delta{q}'):
                    de = abs(v[f'delta{q}'])
                    uno.append((de, amp_abs(pp[0]['parameters']['amp']) * v[f'omegad{q}'] / de,
                                pp[0]['parameters']['duration'] * dt))
            if cmd['name'] == 'cx':
                cr = [s for s in pp if s.get('ch', '').startswith('u') and s.get('pulse_shape') == 'gaussian_square']
                if len(cr) < 2:
                    continue
                k = int(cr[0]['ch'][1:])
                if k not in ctrl or k >= len(ulo):
                    continue
                cq, tq = ctrl[k], ulo[k][0]['q']
                J = v.get(f'jq{min(cq, tq)}q{max(cq, tq)}')
                if not J:
                    continue
                Dl = abs(v[f'wq{cq}'] - v[f'wq{tq}'])
                rcr = amp_abs(cr[0]['parameters']['amp']) * v[f'omegad{cq}'] / Dl
                fin = max(s['t0'] + s['parameters']['duration'] for s in pp)
                dos.append((rcr, Dl, fin * dt, J))
        if uno and dos:
            out.append(dict(b=b.name, n=c.get('n_qubits'), uno=np.median(np.array(uno), axis=0),
                            dos=np.median(np.array(dos), axis=0)))
    return out


C = chips()

# law T|delta|(r) measured by grape_1q.py (4 levels, 1-F < 1e-4); log-log interpolation
R_LEY = np.array([0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.5])
T_LEY = np.array([32.99, 16.49, 12.04, 8.17, 7.07, 6.91, 7.33])


def tmin_1q(r, delta):
    return np.exp(np.interp(np.log(r), np.log(R_LEY), np.log(T_LEY))) / delta


def ejes(fig):
    ax = fig.add_axes([0.0, 0.05, 0.9, 0.92], projection='3d', computed_zorder=False)
    for e in (ax.xaxis, ax.yaxis, ax.zaxis):
        e.pane.set_facecolor('white')
        e.pane.set_edgecolor(REJILLA)
        e._axinfo['grid']['color'] = REJILLA
        e._axinfo['grid']['linewidth'] = 0.4
    ax.tick_params(pad=-1)
    return ax


# ---------- single qubit ----------
fig = plt.figure(figsize=(3.7, 3.4))
ax = ejes(fig)
dmhz = np.linspace(280, 360, 30)                         # |delta|/2pi (MHz) covered by the chips
lr = np.linspace(np.log10(0.06), np.log10(1.0), 40)      # log10 r
DM, LR = np.meshgrid(dmhz, lr)
Z = np.minimum(tmin_1q(10 ** LR, DM * DOS_PI / 1e3), 60)
ax.plot_surface(DM, LR, Z, cmap=cm.Blues, vmin=-10, vmax=60, alpha=0.75, linewidth=0, antialiased=True)
fuera = [ch['b'] for ch in C if ch['uno'][2] > 200]       # toronto: 2560-sample X pulse (special calibration)
for ch in C:
    de, r, tau = ch['uno']
    if tau > 200:
        continue
    dm, l = de / DOS_PI * 1e3, np.log10(r)
    zs = float(tmin_1q(r, de))
    ax.plot([dm, dm], [l, l], [zs, tau], color=TINTA2, lw=0.8)
    ax.scatter([dm], [l], [tau], s=14, c=NARANJA, edgecolors=TINTA, linewidths=0.4, depthshade=False)
    ax.scatter([dm], [l], [zs], s=5, c=AZUL, depthshade=False)
ax.set_xlabel(r'$|\delta|/2\pi$ (MHz)', labelpad=-1)
ax.set_ylabel(r'drive fraction $\Omega/|\delta|$', labelpad=-1)
ax.set_yticks(np.log10([0.1, 0.3, 1.0]))
ax.set_yticklabels(['0.1', '0.3', '1'])
fig.text(-0.06, 0.5, 'X-gate time (ns)', rotation=90, va='center', ha='left', fontsize=8, color=TINTA)  # a 3D
# zlabel falls outside the tight bbox and is clipped
ax.set_zlim(0, 60)
ax.view_init(elev=24, azim=-128)
ax.text2D(0.02, 0.96, 'orange: IBM processor (median)\ngrey line: time above the shortest time found\n'
          f'blue surface: shortest X time found (optimal control)\nnot shown: {", ".join(fuera)} (X pulse > 200 ns)',
          transform=ax.transAxes, fontsize=6.5, color=TINTA, va='top')
fig.savefig(AQUI / 'fig_1q_3d.pdf', bbox_inches='tight', pad_inches=0.06)
plt.close(fig)

# ---------- two qubits ----------
J = float(np.median([ch['dos'][3] for ch in C]))
dc = -DOS_PI * 0.330                                      # rad/ns, median-like transmon anharmonicity


def t_cr(r, Dl):
    nu = J * r * np.abs(dc / (dc + Dl))
    return (np.pi / 2) / nu


fig = plt.figure(figsize=(3.7, 3.4))
ax = ejes(fig)
rr = np.linspace(0.15, 1.0, 30)
Dm = np.linspace(40, 160, 30)                             # |Delta|/2pi MHz
RR, DD = np.meshgrid(rr, Dm)
Z = t_cr(RR, DD * DOS_PI / 1e3)
lim = np.pi / (2 * J)
ax.plot_surface(RR, DD, Z, cmap=cm.Blues, vmin=-200, vmax=Z.max(), alpha=0.75, linewidth=0)
ax.plot_surface(RR, DD, np.full_like(Z, lim), color=NARANJA, alpha=0.18, linewidth=0)
for ch in C:
    r, Dl, t, _ = ch['dos']
    dm = Dl / DOS_PI * 1e3
    if not (0.15 <= r <= 1.0 and 40 <= dm <= 160):
        continue
    zs = float(t_cr(r, Dl))
    ax.plot([r, r], [dm, dm], [zs, t], color=TINTA2, lw=0.8)
    ax.plot([r, r], [dm, dm], [lim, zs], color=AZUL, lw=0.8, ls=':')
    ax.scatter([r], [dm], [t], s=14, c=NARANJA, edgecolors=TINTA, linewidths=0.4, depthshade=False)
ax.set_xlabel(r'CR drive $\Omega_{CR}/\Delta$', labelpad=-1)
ax.set_ylabel(r'detuning $|\Delta|/2\pi$ (MHz)', labelpad=-1)
fig.text(-0.06, 0.5, 'CNOT time (ns)', rotation=90, va='center', ha='left', fontsize=8, color=TINTA)
ax.set_zlim(0, min(1200, Z.max()))
ax.view_init(elev=20, azim=-130)
ax.text2D(0.02, 0.96, f'orange plane: exchange limit $\\pi/2J$ = {lim:.0f} ns\nblue surface: first-order '
          'cross resonance\ndotted: dilution · grey: echo & ramps\norange points: IBM processors (median CX)',
          transform=ax.transAxes, fontsize=6.5, color=TINTA, va='top')
fig.savefig(AQUI / 'fig_2q_3d.pdf', bbox_inches='tight', pad_inches=0.06)
plt.close(fig)
print(f'chips con pulsos: {len(C)}; J mediana {J:.4f} rad/ns; límite de intercambio {lim:.0f} ns')
