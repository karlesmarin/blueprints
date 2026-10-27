# encaje: laboratorios de las cotas del blueprint qsl-diagnostics (dimensión d, tu dispositivo, esfera de Bloch;
# Python puro, Pyodide).
"""Three labs on the formulas of the paper, each with a turnable 3D figure:

- run_qudit: the CZ in d-level transmons (Section VII-B). lambda_d = largest eigenvalue of Q_d = b + b^dagger (sqrt 2
  times the largest Hermite zero), kappa_d = ||b^dagger (x) b + b (x) b^dagger||, both computed here by Sturm bisection
  on symmetric tridiagonal matrices (the exchange operator splits into blocks of fixed excitation number). Bound
  pi/(4 J kappa_d) (entangling-time theorem, Lean), construction pi/(2 J lambda_d^2); ratio 2 kappa_d/lambda_d^2 -> 1
  (Lean: QSL.Exchange.ratio_tendsto_one).
- run_device: the diagnostic on your own numbers. Single qubit: T >= pi/Omega_max (exact X), T >= 2 arcsin(1-e)/Omega_max
  (trace error e; valid for T <= pi/Omega_max), and the model minimum of Table V if |delta| is given. Two qubits: the
  literature qubit-subspace CNOT time pi/(2 j_q), the certified Bell bound (pi/4 - arcsin sqrt(eps))/j_q (Lean), and,
  with the second level, the refined CZ bound 0.4511/j_q and the construction pi/(6 j_q).
- run_bloch: a shaped pulse on the Bloch sphere, integrated exactly step by step: the Mandelstam-Tamm integral of the
  energy spread against the Fubini-Study angle it travels. Fixed axis and f >= 0: ratio exactly 1 (Lean:
  QSL.FixedAxis.mandelstam_tamm_integral_eq_solution); a DRAG quadrature or a detuning bends the path and the ratio
  exceeds 1.
Checked by prueba_labs.py against the table of the paper."""
import json
import math

import labkit as K
import qsl_diagnostics_lab as S
from qsl_data import CHIPS, J_MEDIAN

REFINED = 0.4511064        # T_* >= 0.4511/J, refined CZ bound (cota_cz_refinada.py; lemma 97/32 in Lean)


# ------------------------------------------------------------------ spectra of tridiagonal matrices

def _top(off):
    """Largest eigenvalue of the symmetric tridiagonal matrix with zero diagonal and off-diagonal ``off``."""
    if not off:
        return 0.0
    def below(x):            # number of eigenvalues < x (Sturm sequence of the LDL^T pivots)
        n, q = 0, -x
        if q < 0:
            n += 1
        for e in off:
            q = -x - e * e / (q if q != 0 else 1e-300)
            if q < 0:
                n += 1
        return n
    lo, hi = 0.0, 2 * max(abs(e) for e in off) + 1e-12
    for _ in range(200):
        mid = (lo + hi) / 2
        if below(mid) < len(off) + 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def lam(d):
    """lambda_d: largest eigenvalue of b + b^dagger on d levels."""
    return _top([math.sqrt(k) for k in range(1, d)])


def kappa(d):
    """kappa_d = ||b^dagger (x) b + b (x) b^dagger||: the blocks a + b = N are tridiagonal (hopping sqrt((a+1) b))."""
    best = 0.0
    for N in range(0, 2 * d - 1):
        a_lo, a_hi = max(0, N - d + 1), min(N, d - 1)
        off = [math.sqrt((a + 1) * (N - a)) for a in range(a_lo, a_hi)]
        best = max(best, _top(off))
    return best


# ------------------------------------------------------------------ CZ in d levels

def run_qudit(params):
    p = json.loads(params)
    try:
        d = int(S._num(p, 'd', 3, 2, 40, 'the number of levels d'))
        j = S._num(p, 'j', J_MEDIAN, 0.002, 0.05, 'the coupling J (rad/ns)')
        dmax = int(S._num(p, 'dmax', 20, 4, 40, 'the largest d drawn'))
    except ValueError as e:
        return K.error(str(e))
    dmax = max(dmax, d)
    ds = list(range(2, dmax + 1))
    L = {k: lam(k) for k in ds}
    KA = {k: kappa(k) for k in ds}
    low = lambda k, jj: math.pi / (4 * jj * KA[k])
    up = lambda k, jj: math.pi / (2 * jj * L[k] ** 2)
    js = [0.004 + (0.03 - 0.004) * i / 12 for i in range(13)]
    lg = math.log10
    zlo = lg(min(low(dmax, js[-1]), up(dmax, js[-1])) * 0.8)
    zhi = lg(math.pi / (2 * js[0]) * 1.2)
    items = [K.surface3(lambda k, jj: lg(up(k, jj)), ds, js, 'construction π/(2Jλ_d²): a CZ is reached here (upper)',
                        color='#2E7D32', opacity=0.45),
             K.surface3(lambda k, jj: lg(low(k, jj)), ds, js, 'entangling-time bound π/(4Jκ_d): no CZ below (lower)',
                        color='#1B6F8C', opacity=0.55),
             K.curve3([[2, jj, lg(math.pi / (2 * jj))] for jj in js], 'qubit-only exchange time π/(2J) (d = 2)',
                      color='#B5530F', width=2.5)]
    if dmax >= 3:
        items.append(K.curve3([[3, jj, lg(REFINED / jj)] for jj in js], 'refined bound 0.4511/J (d = 3 only)',
                              color='#6A1B9A', width=2.5, dash=True))
    items.append(K.curve3([[d, j, lg(low(d, j))], [d, j, lg(up(d, j))]], 'the gap at your d and J', color='#C62828',
                          width=3))
    items.append(K.points3([[d, j, lg(up(d, j))], [d, j, lg(low(d, j))]], '', color='#C62828', size=8, star=True))
    box = ((2, dmax), (js[0], js[-1]), (zlo, zhi))
    plot3 = K.three_d(S._scale(items, box), 'CZ time in d-level transmons: the bound (blue) and the construction (green) '
                      'close in as d grows', axes=('levels d: 2 to %d' % dmax, 'J: %.3f to %.3f rad/ns' % (js[0], js[-1]),
                                                   'log10 time (ns): %.1f to %.1f' % (zlo, zhi)))
    ratio = K.svg_plot([{'name': 'construction / bound = 2κ_d/λ_d²', 'x': ds, 'y': [2 * KA[k] / L[k] ** 2 for k in ds],
                         'mode': 'line', 'color': '#1B6F8C'},
                        {'name': 'your d', 'x': [d], 'y': [2 * KA[d] / L[d] ** 2], 'color': '#C62828', 'size': 6},
                        {'name': '1 (tight)', 'x': [2, dmax], 'y': [1, 1], 'mode': 'line', 'color': '#9AA7B0'}],
                       title='How far the construction is from the bound', xlabel='levels d',
                       ylabel='2κ_d / λ_d²')
    t_lo, t_up, t_q = low(d, j), up(d, j), math.pi / (2 * j)
    text = ('With d = %d levels: λ_d = %.6f, κ_d = %.6f. At J = %.4f rad/ns (%s), the entangling-time theorem forbids a CZ '
            'faster than π/(4Jκ_d) = <b>%.1f ns</b> and the quadrature construction reaches one in π/(2Jλ_d²) = '
            '<b>%.1f ns</b>, with ideal (instantaneous) local control; the qubit-only exchange time is %.1f ns. The two '
            'differ by a factor 2κ_d/λ_d² = <b>%.4f</b>%s; it tends to 1 (Lean: ratio_tendsto_one), at rate O(d^(−2/3)) '
            '(Hermite asymptotics, not formalized). %s'
            % (d, L[d], KA[d], j, 'the median of the data' if abs(j - J_MEDIAN) < 1e-9 else 'your value', t_lo, t_up,
               t_q, 2 * KA[d] / L[d] ** 2,
               ' (the interval for the true minimum)' if d != 3 else '',
               'For d = 3 the refined bound raises the floor to 0.4511/J = <b>%.1f ns</b>, so the true minimum lies '
               'in [%.1f, %.1f] ns; the optimizer found 0.55/J = %.1f ns with controls ≤ 10J.'
               % (REFINED / j, REFINED / j, t_up, 0.55 / j) if d == 3 else
               'The refined bound exists only for d = 3.'))
    rows = [[k, '%.6f' % L[k], '%.6f' % KA[k], '%.6f' % (math.pi / (4 * KA[k])), '%.6f' % (math.pi / (2 * L[k] ** 2)),
             '%.4f' % (2 * KA[k] / L[k] ** 2)] for k in ds]
    return K.result(text, [plot3, ratio], K.table(['d', 'λ_d', 'κ_d', 'bound J·T', 'construction J·T', 'ratio'], rows))


# ------------------------------------------------------------------ your device

def _batch(text, e, eps):
    """Your list of gates: one per line, 'name, Omega_max (rad/ns), X ns, j_q (rad/ns), two-qubit ns' (blank fields
    allowed); 'ibm' stands for the IBM per-backend medians, with Omega = the peak drive IBM uses (Omega_peak)."""
    rows = []
    if text.strip().lower() == 'ibm':
        for (name, de, r1, tau, rcr, dl, tcx, jq) in CHIPS:
            rows.append((name, r1 * de, tau, jq, tcx))
    else:
        for k, line in enumerate(text.strip().splitlines(), 1):
            if not line.strip() or line.lstrip().startswith('#'):
                continue
            f = [x.strip() for x in line.split(',')]
            if len(f) != 5:
                raise ValueError('line %d: five fields expected (name, Ω_max, X ns, j_q, 2q ns), got %d' % (k, len(f)))
            try:
                v = [float(x) if x else None for x in f[1:]]
            except ValueError:
                raise ValueError('line %d: a field is not a number' % k)
            if any(x is not None and x <= 0 for x in v):
                raise ValueError('line %d: values must be positive' % k)
            rows.append((f[0] or 'gate %d' % k,) + tuple(v))
    if not rows:
        raise ValueError('no gate in the list')
    if len(rows) > 2000:
        raise ValueError('at most 2000 gates')
    tol1 = 2 * math.asin(1 - e)
    tol2 = math.pi / 4 - math.asin(math.sqrt(eps))
    table, p1, p2, bad = [], [], [], []
    for (name, om, tx, jq, t2) in rows:
        r1 = tx * om / math.pi if om and tx else None
        r1t = tx * om / tol1 if om and tx else None
        r2 = t2 / (math.pi / (2 * jq)) if jq and t2 else None
        r2c = t2 * jq / tol2 if jq and t2 else None
        if r1t is not None and r1t < 1:
            bad.append('%s (single qubit, %.3f)' % (name, r1t))
        if r2c is not None and r2c < 1:
            bad.append('%s (two qubits, %.3f)' % (name, r2c))
        if r1 is not None:
            p1.append([om, jq, r1])      # a blank j_q (or Omega) is placed on the edge of the box (run_device)
        if r2 is not None:
            p2.append([om, jq, r2])
        table.append([name, '%.4g' % om if om else '', '%.4g' % tx if tx else '', '%.2f' % r1 if r1 else '',
                      '%.4g' % jq if jq else '', '%.4g' % t2 if t2 else '', '%.2f' % r2 if r2 else '',
                      '%.2f' % r2c if r2c else ''])
    return rows, table, p1, p2, bad


def _med(v):
    v = sorted(v)
    n = len(v)
    return (v[n // 2] if n % 2 else (v[n // 2 - 1] + v[n // 2]) / 2) if v else float('nan')


def run_device(params):
    p = json.loads(params)
    if str(p.get('batch', '')).strip():
        try:
            e = S._num(p, 'e', 1e-4, 0, 0.5, 'the trace error e')
            eps = S._num(p, 'eps', 1e-3, 0, 0.5, 'the infidelity eps')
            rows, table, p1, p2, bad = _batch(str(p['batch']), e, eps)
        except ValueError as er:
            return K.error(str(er))
        allp = p1 + p2
        xs = [q[0] for q in allp if q[0]] or [1.0]
        ys = [q[1] for q in allp if q[1]] or [0.01]
        zt = max([q[2] for q in allp] + [2.0]) * 1.1
        x0, x1, y0, y1 = min(xs) * 0.9, max(xs) * 1.1, min(ys) * 0.9, max(ys) * 1.1
        for q in allp:                   # blank fields: on the near edge of the box, not at 0 (outside it)
            q[0] = q[0] or x0
            q[1] = q[1] or y0
        items = [K.surface3(lambda x, y: 1.0, [x0, x1], [y0, y1], 'ratio 1: the speed limit; nothing exact can go '
                            'below this glass', color='#C62828', opacity=0.18)]
        if p1:
            items.append(K.points3([q for q in p1 if q[2] >= 1], 'single-qubit X: duration / (π/Ω_max)',
                                   color='#1B6F8C', size=6))
            items += [K.curve3([[q[0], q[1], 1], [q[0], q[1], q[2]]], '', color='#1B6F8C', width=1) for q in p1]
        if p2:
            items.append(K.points3([q for q in p2 if q[2] >= 1], 'two-qubit gate: duration / (π/(2j_q))',
                                   color='#B5530F', size=6))
            items += [K.curve3([[q[0], q[1], 1], [q[0], q[1], q[2]]], '', color='#B5530F', width=1) for q in p2]
        under = [q for q in p1 + p2 if q[2] < 1]
        if under:
            items.append(K.points3(under, 'below ratio 1: see the summary', color='#C62828', size=10, star=True))
        box = ((x0, x1), (y0, y1), (0, zt))
        plot = K.three_d(S._scale(items, box), 'Your gates above the speed limit: height = duration / limit',
                         axes=('Ω_max: %.3g to %.3g rad/ns' % (x0, x1), 'j_q: %.3g to %.3g rad/ns' % (y0, y1),
                               'ratio: 0 to %.3g' % zt))
        m1, m2 = _med([q[2] for q in p1]), _med([q[2] for q in p2])
        ibm = str(p['batch']).strip().lower() == 'ibm'
        text = ('%d gates%s. Single qubit (%d): median duration/(π/Ω_max) <b>%s</b>. Two qubits (%d): median '
                'duration/(π/(2j_q)) <b>%s</b> (literature bound); the certified Bell bound at ε = %g is %.3f/j_q. %s%s'
                % (len(rows), ' (IBM per-backend medians, Ω = the peak drive IBM uses, not the full amplitude)' if ibm
                   else '', len(p1), '%.2f' % m1 if p1 else '—', len(p2), '%.2f' % m2 if p2 else '—', eps,
                   math.pi / 4 - math.asin(math.sqrt(eps)),
                   (('<b>Below the floor:</b> %s — the paper\'s falsifier fires (tolerances e = %g, ε = %g).'
                     % (', '.join(bad[:10]), e, eps)) if bad else 'No gate is below its certified floor.') +
                   (' %d two-qubit gate(s) beat π/(2j_q) without breaking the certified bound: impossible inside the '
                    'qubit subspace, so either j_q is not the coupling that acts or the gate uses higher levels.'
                    % sum(q[2] < 1 for q in p2) if any(q[2] < 1 for q in p2) else ''),
                   ' At the peak drive IBM uses the single-qubit ratio is about 2 (paper: shape factor 1.87–2.16).'
                   if ibm else ''))
        return K.result(text, [plot], K.table(['gate', 'Ω_max', 'X ns', 'X / (π/Ω)', 'j_q', '2q ns',
                                               '2q / (π/2j_q)', '2q / Bell bound (ε)'], table))
    try:
        om = S._num(p, 'omega', 0.727, 0.01, 10, 'Omega_max (rad/ns)')
        tx = S._num(p, 'tx', 35.6, 0.1, 5000, 'the X duration (ns)')
        e = S._num(p, 'e', 1e-4, 0, 0.5, 'the trace error e')
        mhz = S._num(p, 'delta_mhz', 330, 0, 600, '|delta|/2pi (MHz; 0 = not given)')
        jq = S._num(p, 'jq', 0.01268, 0.0005, 0.2, 'j_q (rad/ns)')
        t2 = S._num(p, 't2q', 548, 1, 20000, 'the two-qubit duration (ns)')
        eps = S._num(p, 'eps', 1e-3, 0, 0.5, 'the infidelity eps')
    except ValueError as er:
        return K.error(str(er))
    q_exact = math.pi / om
    q_tol = 2 * math.asin(1 - e) / om
    r = om / S.rad_ns(mhz) if mhz > 0 else None
    model = S.t_x_ns(r, mhz) if r is not None and 0.1 <= r <= 1.5 else None
    lit = math.pi / (2 * jq)
    bell = (math.pi / 4 - math.asin(math.sqrt(eps))) / jq
    ref, constr = REFINED / jq, math.pi / (6 * jq)
    lg = math.log10
    # 3D 1: the single-qubit floor over (Omega, log10 e); your gate floats above it
    oms = [om * (0.4 + 1.2 * i / 12) for i in range(13)]
    es = [-6 + 5.7 * i / 12 for i in range(13)]       # log10 e from 1e-6 to 0.5
    floor1 = lambda o, le: 2 * math.asin(1 - 10 ** le) / o
    zmax1 = max(tx, floor1(oms[0], es[0])) * 1.1
    it1 = [K.surface3(floor1, oms, es, 'certified floor 2 arcsin(1−e)/Ω_max (Lean, two-level)', color='#1B6F8C',
                      opacity=0.5),
           K.curve3([[om, lg(max(e, 1e-6)), q_tol], [om, lg(max(e, 1e-6)), tx]], 'your gap', color='#C62828', width=3),
           K.points3([[om, lg(max(e, 1e-6)), tx]], 'your X gate', color='#C62828', size=10, star=True)]
    if model is not None:
        it1.append(K.points3([[om, lg(max(e, 1e-6)), model]], 'optimal control on IBM\'s model (Table V)',
                             color='#2E7D32', size=8))
    box1 = ((oms[0], oms[-1]), (es[0], es[-1]), (0, zmax1))
    p1 = K.three_d(S._scale(it1, box1), 'Single qubit: the floor no pulse can go under, and your gate above it',
                   axes=('Ω_max: %.2f to %.2f rad/ns' % (oms[0], oms[-1]), 'log10 e: −6 to −0.3',
                         'X time: 0 to %.0f ns' % zmax1))
    # 3D 2: the two-qubit floors over (j_q, log10 eps)
    jjs = [jq * (0.4 + 1.2 * i / 12) for i in range(13)]
    floor2 = lambda jj, le: (math.pi / 4 - math.asin(math.sqrt(10 ** le))) / jj
    zmax2 = max(t2, math.pi / (2 * jjs[0])) * 1.1
    le = lg(max(eps, 1e-6))
    it2 = [K.surface3(floor2, jjs, es, 'certified Bell floor (π/4 − arcsin√ε)/j_q (Lean)', color='#1B6F8C', opacity=0.5),
           K.surface3(lambda jj, l_: math.pi / (2 * jj), jjs, es, 'qubit-subspace CNOT time π/(2j_q) (literature)',
                      color='#B5530F', opacity=0.25),
           K.curve3([[jq, le, bell], [jq, le, t2]], 'your gap', color='#C62828', width=3),
           K.points3([[jq, le, t2]], 'your two-qubit gate', color='#C62828', size=10, star=True),
           K.points3([[jq, le, ref], [jq, le, constr]], 'second level: refined bound and construction (CZ)',
                     color='#6A1B9A', size=7)]
    box2 = ((jjs[0], jjs[-1]), (es[0], es[-1]), (0, zmax2))
    p2 = K.three_d(S._scale(it2, box2), 'Two qubits: the certified floor, the literature plane, and your gate',
                   axes=('j_q: %.4f to %.4f rad/ns' % (jjs[0], jjs[-1]), 'log10 ε: −6 to −0.3',
                         'gate time: 0 to %.0f ns' % zmax2))
    text = ('<b>Single qubit.</b> Ω_max = %.3f rad/ns: an exact X needs at least π/Ω_max = %.2f ns; with trace error '
            'e = %g, at least 2 arcsin(1−e)/Ω_max = %.2f ns. Your %.1f ns gate is <b>%.2f×</b> the exact limit '
            '(<b>%.2f×</b> the tolerant one)%s.%s '
            '<b>Two qubits.</b> j_q = %.5f rad/ns: the known qubit-subspace CNOT time π/(2j_q) = %.1f ns gives the '
            'ratio <b>%.2f</b> (the paper\'s 4.22 is the median of the 1758 per-pair ratios, not the ratio of the '
            'medians used as defaults here); the certified bound (a Bell vector to fidelity 1−ε = %g) is %.1f ns, ratio '
            '<b>%.2f</b>. If the second transmon level is used with ideal local control, a CZ-class gate cannot beat '
            '0.4511/j_q = %.1f ns and is reachable in π/(6j_q) = %.1f ns. Bounds hold for the model\'s Hamiltonian '
            'norms; the ratios are only as good as Ω_max and j_q.'
            % (om, q_exact, e, q_tol, tx, tx / q_exact, tx / q_tol,
               '' if tx >= q_tol else ' — <b>below the floor</b>: the convention or the data is wrong (the paper\'s '
               'falsifier)',
               (' At r = Ω_max/|δ| = %.3f, the Table V interpolation (4 levels, feasible times found on a coarse grid, '
                'so an upper bound on the true minimum) gives %.1f ns: your gate is %.1f× that.%s'
                % (r, model, tx / model,
                   ' The paper\'s dedicated search at this r (r_full = 0.351) found 4.8 ns, against the bound ≥ 4.3 ns.'
                   if abs(r - 0.351) < 0.005 else '')) if model is not None else
               (' The model minimum needs 0.1 ≤ Ω_max/|δ| ≤ 1.5 (here %.3f).' % r if r is not None else ''),
               jq, lit, t2 / lit, 1 - eps, bell, t2 / bell, ref, constr))
    rows = [['single qubit', 'π/Ω_max (exact X)', '%.2f' % q_exact, '%.2f' % (tx / q_exact), 'Lean'],
            ['single qubit', '2 arcsin(1−e)/Ω_max', '%.2f' % q_tol, '%.2f' % (tx / q_tol), 'Lean'],
            ['two qubits', 'π/(2j_q), qubit subspace', '%.1f' % lit, '%.2f' % (t2 / lit), 'literature'],
            ['two qubits', '(π/4 − arcsin√ε)/j_q, Bell', '%.1f' % bell, '%.2f' % (t2 / bell), 'Lean'],
            ['two qubits, 3 levels', '0.4511/j_q, CZ refined', '%.1f' % ref, '%.2f' % (t2 / ref), 'lemma in Lean'],
            ['two qubits, 3 levels', 'π/(6j_q), construction', '%.1f' % constr, '%.2f' % (t2 / constr), 'reachable']]
    if model is not None:
        rows.insert(2, ['single qubit', 'optimal control, Table V interpolated', '%.2f' % model, '%.2f' % (tx / model),
                        'feasible (upper)'])
    return K.result(text, [p1, p2], K.table(['gate', 'floor', 'time (ns)', 'your ratio', 'status'], rows))


# ------------------------------------------------------------------ the Bloch sphere

def _shape(kind, x, samples=None):
    """Envelope on x in [0, 1] (unnormalised) and its derivative in x; 'custom': your samples, equally spaced over
    [0, 1] and joined linearly (a sign change makes the axis flip: the equality case needs f >= 0)."""
    if kind == 'custom':
        m = len(samples) - 1
        k = min(int(x * m), m - 1)
        a = x * m - k
        return samples[k] + a * (samples[k + 1] - samples[k]), (samples[k + 1] - samples[k]) * m
    if kind == 'square':
        return 1.0, 0.0
    if kind == 'sine':
        return math.sin(math.pi * x), math.pi * math.cos(math.pi * x)
    s = 0.18                                          # gaussian, sigma = T/5.5 or so, edges subtracted
    g = math.exp(-(x - 0.5) ** 2 / (2 * s * s)) - math.exp(-0.25 / (2 * s * s))
    return g, -(x - 0.5) / (s * s) * math.exp(-(x - 0.5) ** 2 / (2 * s * s))


def _step(psi, hx, hy, hz, dt):
    """psi <- exp(-i dt (hx X + hy Y + hz Z)/2) psi, exactly."""
    n = math.sqrt(hx * hx + hy * hy + hz * hz)
    if n == 0:
        return psi
    c, s = math.cos(n * dt / 2), math.sin(n * dt / 2) / n
    a, b = psi
    # (c I - i s (hx X + hy Y + hz Z)) psi
    return (c * a - 1j * s * (hz * a + (hx - 1j * hy) * b), c * b - 1j * s * ((hx + 1j * hy) * a - hz * b))


def _bloch(psi):
    a, b = psi
    return [2 * (a.conjugate() * b).real, 2 * (a.conjugate() * b).imag, abs(a) ** 2 - abs(b) ** 2]


def run_bloch(params):
    p = json.loads(params)
    kind = str(p.get('shape', 'gaussian')).strip().lower()
    if kind not in ('square', 'sine', 'gaussian', 'custom'):
        return K.error('shape is square, sine, gaussian or custom (then give the samples)')
    samples = None
    if kind == 'custom':
        try:
            samples = [float(x) for x in str(p.get('samples', '')).replace(';', ',').split(',') if x.strip()]
        except ValueError:
            return K.error('the samples are numbers separated by commas')
        if len(samples) < 2 or len(samples) > 400:
            return K.error('give between 2 and 400 samples of the envelope')
        if sum(samples) == 0:
            return K.error('the samples have zero area')
    try:
        T = S._num(p, 'T', 20, 1, 500, 'the duration T (ns)')
        area = S._num(p, 'area', 1, 0.05, 2, 'the pulse area (units of π)')
        beta = S._num(p, 'beta', 0, -3, 3, 'the DRAG weight β in ns (quadrature β·df/dt)')
        det = S._num(p, 'detuning_mhz', 0, -50, 50, 'the detuning Δ/2π (MHz)')
    except ValueError as er:
        return K.error(str(er))
    n = 600
    dt = T / n
    xs = [(k + 0.5) / n for k in range(n)]
    f = [_shape(kind, x, samples) for x in xs]
    norm = sum(v for v, _ in f) * dt
    amp = area * math.pi / norm                       # in-phase drive f(t) = amp*env, area = area*pi
    hz = S.rad_ns(det)
    psi = (1 + 0j, 0j)
    path, mt, peak = [[0.0, 0.0, 1.0]], 0.0, 0.0
    frames, labels = [], []
    for k in range(n):
        hx = amp * f[k][0]
        hy = beta * amp * f[k][1] / T              # DRAG quadrature beta * df/dt (beta in ns)
        r = _bloch(psi)
        h2 = hx * hx + hy * hy + hz * hz
        hr = hx * r[0] + hy * r[1] + hz * r[2]
        mt += 0.5 * math.sqrt(max(h2 - hr * hr, 0.0)) * dt   # Delta E = |h x r|/2 for H = h.sigma/2
        peak = max(peak, math.sqrt(hx * hx + hy * hy))
        psi = _step(psi, hx, hy, hz, dt)
        path.append(_bloch(psi))
        if (k + 1) % 50 == 0:
            frames.append([K.points3([path[-1]], 'the state at this time', color='#C62828', size=9, star=True),
                           K.curve3([[0, 0, 0], path[-1]], '', color='#C62828', width=1.5)])
            labels.append('t = %.1f ns, MT so far %.3f' % ((k + 1) * dt, mt))
    ov = abs(psi[0])                                  # |<0|psi_T>|
    ang = math.acos(min(1.0, ov))
    grid = [[[math.sin(th) * math.cos(ph), math.sin(th) * math.sin(ph), math.cos(th)]
             for ph in [2 * math.pi * j / 24 for j in range(25)]] for th in [math.pi * i / 12 for i in range(13)]]
    items = [{'type': 'surface', 'grid': grid, 'color': '#c9d6e3', 'opacity': 0.18, 'name': 'Bloch sphere'},
             K.curve3(path, 'the path of the state from |0⟩ (north pole)', color='#1B6F8C', width=2.6),
             K.curve3([[0, 0, 1], [0, 0, -1]], '', color='#9AA7B0', width=1, dash=True),
             K.points3([[0, 0, 1]], '|0⟩', color='#2E7D32', size=7), K.points3([[0, 0, -1]], '|1⟩', color='#B5530F', size=7)]
    plot = K.three_d(items, 'The pulse on the Bloch sphere: ▶ runs the time', axes=('x', 'y', 'z'),
                     slider={'label': 'time', 'values': labels, 'items': frames, 'start': len(frames) - 1})
    sat = abs(mt - ang) < 1e-3 * max(ang, 1e-9)
    text = ('A %s pulse of area %gπ in T = %g ns (peak drive %.3f rad/ns)%s%s. The Mandelstam–Tamm integral '
            '∫ΔE dt = <b>%.4f</b>; the Fubini–Study angle actually travelled, arccos|⟨0|ψ_T⟩| = <b>%.4f</b>; ratio '
            '<b>%.4f</b>. %s Final population of |1⟩: %.6f. Against the two-level limit π/Ω_peak = %.2f ns this pulse '
            'is %.2f× longer: the shape costs time even when the speed limit is saturated.'
            % (kind, area, T, peak, ', DRAG β = %g' % beta if beta else '', ', detuning %g MHz' % det if det else '',
               mt, ang, mt / ang if ang > 0 else float('nan'),
               ('Fixed axis, f ≥ 0: the bound is met with <b>equality</b>, whatever the shape (Lean: '
                'FixedAxis.mandelstam_tamm_integral_eq_solution). This is why a speed-limit estimator read on a π pulse '
                'returns ratio 1 by construction.' if sat else
                'The axis moves (quadrature, detuning, or an envelope that changes sign): the path bends away from the meridian and the integral '
                'exceeds the angle; the equality case no longer applies.'),
               abs(psi[1]) ** 2, math.pi / peak, T / (math.pi / peak)))
    return K.result(text, [plot])
