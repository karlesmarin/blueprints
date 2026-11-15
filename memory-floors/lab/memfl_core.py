# encaje: núcleo numérico (Python puro, Pyodide) de los laboratorios de memory-floors: P*, P_phi, c*, r_res, B_p/B_c y el
# ciclo sin reinicio. Reproduce cerrada_y_desfase.py, tabla_experimentos.py y ciclo_sin_reset/ de research/qsl-hardware/
# memoria sin numpy ni scipy (exponencial de matriz por Taylor con escalado). No es herramienta de Excovery.
"""Pure-Python numerics for the labs of «Exact limits on writing a superconducting quantum memory».

Conventions of the paper: G = coupling bound, gq/gm = relaxation rates 1/T1 of qubit and mode, eq/em = coherence-decay
rates 1/T2, phi = eta - gamma/2 = pure dephasing (clamped at 0), F = phi_q + phi_m, Gamma = (gq+gm)/2 + F.
Population block (p_a, p_b, Im rho_ab) of the resonant pulse: M = [[-gq,0,-2G],[0,-gm,2G],[G,-G,-Gamma]].
Sources (checked by comprueba_lab.py): numeros.py, tabla_experimentos.py, cerrada_y_desfase.py, ciclo_sin_reset/."""
import math

P2 = 2 * math.pi


# ------------------------------------------------------------------ small linear algebra (lists of lists)

def _mm(A, B):
    n, m, k = len(A), len(B[0]), len(B)
    return [[sum(A[i][l] * B[l][j] for l in range(k)) for j in range(m)] for i in range(n)]


def expm(A):
    """e^A by scaling and squaring with a Taylor series (real or complex entries, any small size)."""
    n = len(A)
    nrm = max(sum(abs(x) for x in row) for row in A)
    s = 0
    while nrm > 0.5:
        nrm /= 2
        s += 1
    B = [[x / (2 ** s) for x in row] for row in A]
    I = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    E, T = [r[:] for r in I], [r[:] for r in I]
    for k in range(1, 16):
        T = [[x / k for x in row] for row in _mm(T, B)]
        E = [[E[i][j] + T[i][j] for j in range(n)] for i in range(n)]
    for _ in range(s):
        E = _mm(E, E)
    return E


def expv(A, v, dt):
    """e^{A dt} v by a Taylor series on the vector, in as many sub-steps as the norm needs."""
    n = len(v)
    nrm = max(sum(abs(x) for x in row) for row in A) * abs(dt)
    m = max(1, int(math.ceil(nrm)))
    h = dt / m
    for _ in range(m):
        term, acc = v, list(v)
        for k in range(1, 17):
            term = [sum(A[i][j] * term[j] for j in range(n)) * (h / k) for i in range(n)]
            acc = [acc[i] + term[i] for i in range(n)]
        v = acc
    return v


def matvec(S, v):
    return [S[0][0] * v[0] + S[0][1] * v[1] + S[0][2] * v[2], S[1][0] * v[0] + S[1][1] * v[1] + S[1][2] * v[2],
            S[2][0] * v[0] + S[2][1] * v[1] + S[2][2] * v[2]]


# ------------------------------------------------------------------ rates and the resonant pulse

def rates(T1q, T2q, T1m, T2m):
    """(gq, gm, eq, em, fq, fm): relaxation, coherence-decay and pure-dephasing rates (1/us when T in us)."""
    gq, gm, eq, em = 1 / T1q, 1 / T1m, 1 / T2q, 1 / T2m
    return gq, gm, eq, em, max(eq - gq / 2, 0.0), max(em - gm / 2, 0.0)


def mat_M(G, gq, gm, F):
    return [[-gq, 0.0, -2 * G], [0.0, -gm, 2 * G], [G, -G, -((gq + gm) / 2 + F)]]


def p_res_at(G, gq, gm, F, t):
    """p_res(t) = (e^{Mt})_{21}: population transferred by the resonant pulse g = G, D = 0, stopped at t."""
    E = expm([[x * t for x in row] for row in mat_M(G, gq, gm, F)])
    return E[1][0]


def p_res_series(G, gq, gm, F, dt, n, t_start=0.0):
    """p_res at t_start + k dt, k = 0..n (one matrix exponential, then repeated products)."""
    M = mat_M(G, gq, gm, F)
    S = expm([[x * dt for x in row] for row in M])
    v = [1.0, 0.0, 0.0] if t_start == 0 else expv(M, [1.0, 0.0, 0.0], t_start)
    out = [v[1]]
    for _ in range(n):
        v = matvec(S, v)
        out.append(v[1])
    return out


def _golden_max(f, a, b, it=40):
    g = (math.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(it):
        if fc > fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a)
            fd = f(d)
    x = (a + b) / 2
    return x, f(x)


def _parab(y0, y1, y2):
    """Vertex of the parabola through three equally spaced samples: (offset in steps, value)."""
    den = y0 - 2 * y1 + y2
    if den == 0:
        return 0.0, y1
    h = 0.5 * (y0 - y2) / den
    return h, y1 - 0.25 * (y0 - y2) * h


def p_phi(G, gq, gm, F, refine=True, horizon=8.0):
    """P_phi = sup_t p_res(t) and a time where it is reached; (value, t, attained). ``attained`` is False when the
    maximum of the scan is at its end (a supremum not reached, as for strong dephasing)."""
    t0 = math.pi / (2 * G)
    dt = t0 / 100
    n = int(horizon * 100)
    s = p_res_series(G, gq, gm, F, dt, n)
    k = max(range(len(s)), key=lambda i: s[i])
    if k == 0 or k == n:
        return s[k], k * dt, False
    if not refine:
        h, v = _parab(s[k - 1], s[k], s[k + 1])
        return v, (k + h) * dt, True
    x, v = _golden_max(lambda t: p_res_at(G, gq, gm, F, t), (k - 1) * dt, (k + 1) * dt)
    return v, x, True


def p_star(G, gq, gm):
    """Theorem 1 (all three regimes): P* = 4G^2/(4G^2+gq gm) e^{-gb t*}; returns (P*, t*, regime)."""
    gb = (gq + gm) / 2
    d = gq - gm
    pref = 4 * G * G / (4 * G * G + gq * gm)
    if gb == 0:
        return 1.0, math.pi / (2 * G), 'lossless'
    disc = G * G - d * d / 16
    if abs(disc) < 1e-14 * G * G:
        ts = 2 / gb
        return pref * math.exp(-gb * ts), ts, 'critical'
    if disc > 0:
        W = math.sqrt(disc)
        ts = math.atan2(2 * W, gb) / W
        return pref * math.exp(-gb * ts), ts, 'under-damped'
    k = math.sqrt(-disc)
    ts = math.atanh(2 * k / gb) / k
    return pref * ((gb - 2 * k) / (gb + 2 * k)) ** (gb / (2 * k)), ts, 'over-damped'


def folk(G, gq, gm):
    """The familiar estimate of the loss, 1 - exp(-pi (gq+gm)/(4G))."""
    return 1 - math.exp(-math.pi * (gq + gm) / (4 * G))


def c_star(G, eq, em):
    return math.sqrt(p_star(G, 2 * eq, 2 * em)[0])


def c_res(G, eq, em, t):
    """c_res(t) = G e^{-(eq+em)t/2} |sin(w t)|/w, w^2 = G^2 - (eq-em)^2/4 (sinh when over-damped)."""
    w2 = G * G - (eq - em) ** 2 / 4
    e = math.exp(-(eq + em) * t / 2)
    if abs(w2) < 1e-14:
        return G * e * t
    if w2 > 0:
        w = math.sqrt(w2)
        return G * e * abs(math.sin(w * t)) / w
    k = math.sqrt(-w2)
    return G * e * math.sinh(k * t) / k


def r_of(p, c):
    return (1 - p) / 6 + (1 - c) / 3


def r_sep(G, T1q, T2q, T1m, T2m, refine=True):
    gq, gm, eq, em, fq, fm = rates(T1q, T2q, T1m, T2m)
    ph = p_phi(G, gq, gm, fq + fm, refine)[0]
    return r_of(ph, c_star(G, eq, em)), ph


def r_res(G, T1q, T2q, T1m, T2m, refine=True):
    """r_res = min_t [(1-p_res)/6 + (1-c_res)/3] over 0.4..1.3 pi/(2G) (as tabla_experimentos.franja); (r, t)."""
    gq, gm, eq, em, fq, fm = rates(T1q, T2q, T1m, T2m)
    F = fq + fm
    t0 = math.pi / (2 * G)
    dt = t0 / 400
    n = int(0.9 * 400)
    s = p_res_series(G, gq, gm, F, dt, n, 0.4 * t0)
    rr = [r_of(s[i], c_res(G, eq, em, 0.4 * t0 + i * dt)) for i in range(len(s))]
    k = min(range(len(rr)), key=lambda i: rr[i])
    if k == 0 or k == len(rr) - 1:
        return rr[k], 0.4 * t0 + k * dt
    if not refine:
        h, v = _parab(-rr[k - 1], -rr[k], -rr[k + 1])
        return -v, 0.4 * t0 + (k + h) * dt
    x, v = _golden_max(lambda t: -r_of(p_res_at(G, gq, gm, F, t), c_res(G, eq, em, t)),
                       0.4 * t0 + (k - 1) * dt, 0.4 * t0 + (k + 1) * dt)
    return -v, x


# ------------------------------------------------------------------ devices: parameters of the paper (cited)

# ETH MRQC 2601.07825 (numeros.py, tabla_experimentos.FILAS): transmon T1 = 30 us, T2 (echo) = 23 us, g/2pi = 0.296 MHz;
# modes 1, 2, 3 of Table 1: (T1, T2) of the phonon mode in us.
G_ETH = P2 * 0.296
ETH_Q = (30.0, 23.0)
ETH_MODES = {1: (196.0, 368.0), 2: (137.0, 250.0), 3: (64.0, 127.0)}
# Caltech 2412.08006, oscillator A (tabla_experimentos.FILAS)
G_CALTECH_A = P2 * 0.200
CALTECH_A = (1.70, 1.30, 19300.0, 562.0)

# Rutgers 2503.10623, per mode (tabla_experimentos.RUTGERS): (tau_pi ns, F train, F Rabi, F simulation, T1 ms, T2* ms of
# the cavity); transmon {g,f}: T1(f->e) 28.85 us, T2* 36.58 us (without pump).
RUTGERS = [(328.1, 0.97687, 0.97755, 0.99159, 1.187, 1.932), (189.2, 0.98080, 0.99020, 0.99409, 1.253, 2.044),
           (193.0, 0.99037, 0.99328, 0.99420, 1.298, 2.0243), (207.2, 0.98650, 0.99061, 0.99386, 1.175, 1.926),
           (184.2, 0.98348, 0.99261, 0.99387, 1.175, 1.897), (369.7, 0.98011, 0.98777, 0.99036, 0.899, 1.559),
           (272.1, 0.98543, 0.98663, 0.99198, 0.656, 1.1613), (287.2, 0.98567, 0.98809, 0.99105, 0.851, 1.555),
           (359.2, 0.98531, 0.98381, 0.98928, 0.936, 1.662), (332.9, 0.97904, 0.98081, 0.98822, 0.989, 1.811)]
RUTGERS_Q = (28.85, 36.58)


def rutgers_limit(i, T1q, T2q, refine=True):
    """1 - P_phi (population not transferred, the limit of Table 3) for Rutgers mode i (0-based), in per cent."""
    tau, Ft, Fr, Fs, T1c, T2c = RUTGERS[i]
    G = math.pi / (2 * tau * 1e-3)
    gq, gm, eq, em, fq, fm = rates(T1q, T2q, 1000 * T1c, min(1000 * T2c, 2000 * T1c))
    return 100 * (1 - p_phi(G, gq, gm, fq + fm, refine)[0])


# ------------------------------------------------------------------ envelopes B_p, B_c (Corollary 8) and r_time

def envelopes(G, T1q, T2q, T1m, T2m, gt_end, dgt=2e-4):
    """On the grid G t = k dgt, k = 0..gt_end/dgt: p_res, c_res, B_p, B_c (running weighted maxima).
    Returns dict of lists plus the rates."""
    gq, gm, eq, em, fq, fm = rates(T1q, T2q, T1m, T2m)
    F = fq + fm
    mu, nu = min(gq, gm), min(eq, em)
    dt = dgt / G
    n = int(round(gt_end / dgt))
    pr = p_res_series(G, gq, gm, F, dt, n)
    ts = [i * dt for i in range(n + 1)]
    cr = [c_res(G, eq, em, t) for t in ts]
    Bp, Bc = [], []
    mp = mc = 0.0
    for t, p, c in zip(ts, pr, cr):
        mp = max(mp, math.exp(mu * t) * p)
        mc = max(mc, math.exp(nu * t) * c)
        Bp.append(math.exp(-mu * t) * mp)
        Bc.append(math.exp(-nu * t) * mc)
    return {'t': ts, 'gt': [G * t for t in ts], 'p': pr, 'c': cr, 'Bp': Bp, 'Bc': Bc, 'mu': mu, 'nu': nu, 'dt': dt}


def peak(y, dx):
    """(index-refined position in units of dx, value) of the maximum of the samples y."""
    k = max(range(len(y)), key=lambda i: y[i])
    if k == 0 or k == len(y) - 1:
        return k * dx, y[k]
    h, v = _parab(y[k - 1], y[k], y[k + 1])
    return (k + h) * dx, v


# ------------------------------------------------------------------ random piecewise-constant pulses (Theorem 2 test)

def pop_pulse(T, mods, phases, dets, gq, gm, F):
    """p_b(T) for a piecewise-constant complex coupling g_k = mods_k e^{i phases_k} and detuning dets_k (one-excitation
    Lindblad block, as cerrada_y_desfase.pob_pulso); segments of equal length T/n."""
    n = len(mods)
    Gam = (gq + gm) / 2 + F
    v = [1 + 0j, 0j, 0j, 0j]
    for k in range(n):
        g = mods[k] * complex(math.cos(phases[k]), math.sin(phases[k]))
        gc = g.conjugate()
        D = dets[k]
        L = [[-gq, 0, 1j * gc, -1j * g], [0, -gm, -1j * gc, 1j * g],
             [1j * g, -1j * g, -(1j * D + Gam), 0], [-1j * gc, 1j * gc, 0, -(-1j * D + Gam)]]
        v = expv(L, v, T / n)
    return v[1].real


# ------------------------------------------------------------------ the memory cycle (write - wait - read)

def rho_dens(P, gq, gm, fq, fm):
    """First-order error density rho(P) of a lossless path with qubit population P (paper, after Prop. cycle)."""
    return (gq * P + fq * P * (2 - P) + gm * (1 - P) + fm * (1 - P * P)) / 3


def r1_cycle(G, par, t, th, steps=400):
    """First-order cost of the cycle parked at angle th (P_w = cos^2 th): (2/G) int_0^th rho(cos^2 u) du + t rho(cos^2 th),
    by Simpson's rule on a polynomial in cos^2 (exact at this resolution)."""
    gq, gm, fq, fm = par
    n = steps if steps % 2 == 0 else steps + 1
    h = th / n
    f = [rho_dens(math.cos(i * h) ** 2, gq, gm, fq, fm) for i in range(n + 1)]
    I = (f[0] + f[n] + 4 * sum(f[1:n:2]) + 2 * sum(f[2:n - 1:2])) * h / 3 if th > 0 else 0.0
    return 2 * I / G + t * rho_dens(math.cos(th) ** 2, gq, gm, fq, fm)


def r1_min(G, par, t):
    """Minimum over the parking angle th in [0, pi/2] of the first-order cost: (r1*, th*)."""
    cand = [(r1_cycle(G, par, t, math.pi / 2), math.pi / 2)]
    x, v = _golden_max(lambda th: -r1_cycle(G, par, t, th), 0.0, math.pi / 2, it=60)
    cand.append((-v, x))
    cand.append((r1_cycle(G, par, t, 0.0), 0.0))
    return min(cand)


def t_c_first_order(G, par, n=4000):
    """Memory-utility threshold of Prop. noreset: t_c = min A(th)/d(th) over d > 0, A(th) = (2/G) int_0^th rho,
    d(th) = rho(1) - rho(cos^2 th) (closed-form primitive). (None, None) when gm + fm >= gq + fq (no access is optimal
    for every wait). Grid plus golden refinement; the paper certifies t_c for mode 1 by interval arithmetic."""
    gq, gm, fq, fm = par
    if gm + fm >= gq + fq:
        return None, None
    a, b, c = (gm + fm) / 3, (gq + 2 * fq - gm) / 3, -(fq + fm) / 3

    def A(th):
        i2 = th / 2 + math.sin(2 * th) / 4
        i4 = 3 * th / 8 + math.sin(2 * th) / 4 + math.sin(4 * th) / 32
        return 2 / G * (a * th + b * i2 + c * i4)

    def ratio(th):
        P = math.cos(th) ** 2
        d = (a + b + c) - (a + b * P + c * P * P)
        return A(th) / d if d > 0 else float('inf')

    ths = [math.pi / 2 * k / n for k in range(1, n + 1)]
    k = min(range(n), key=lambda i: ratio(ths[i]))
    lo, hi = ths[max(k - 1, 0)], ths[min(k + 1, n - 1)]
    th, v = _golden_max(lambda x: -ratio(x), lo, hi, it=60)
    return -v, th


def gain_closed(G, par, t):
    """(gm+fm)^2 / (3 G^2 (gq+2 fq-gm) t) and delta* = (gm+fm)/(G t (gq+2 fq-gm)); None if gq+2 fq <= gm."""
    gq, gm, fq, fm = par
    k = gq + 2 * fq - gm
    if k <= 0 or t <= 0:
        return None, None
    return (gm + fm) ** 2 / (3 * G * G * k * t), (gm + fm) / (G * t * k)


def floor_with_reset(G, T1q, T2q, T1m, T2m, t):
    """Proposition (memory cycle with a reset): [1 - Pphi^2 e^{-gm t}]/6 + [1 - c*^2 e^{-eta_m t}]/3."""
    gq, gm, eq, em, fq, fm = rates(T1q, T2q, T1m, T2m)
    ph = p_phi(G, gq, gm, fq + fm)[0]
    cs = c_star(G, eq, em)
    return (1 - ph ** 2 * math.exp(-gm * t)) / 6 + (1 - cs ** 2 * math.exp(-em * t)) / 3


def cycle_exact(G, T1q, T2q, T1m, T2m, t, th_w, th_r=None):
    """Exact cost r = (1-p)/6 + (1-c)/3 of the cycle WITHOUT reset made of two resonant pulses: write g = +G for
    G t_w = th_w, wait t (g = 0), read g = -G for G t_r = th_r (th_r = th_w by default; read phase pi). p = qubit population
    at the end (one-excitation block, 4 variables), c = |a_q| (amplitude equations with the coherence rates)."""
    if th_r is None:
        th_r = th_w
    gq, gm, eq, em, fq, fm = rates(T1q, T2q, T1m, T2m)
    Gam = (gq + gm) / 2 + fq + fm
    v = [1 + 0j, 0j, 0j, 0j]
    a = [1 + 0j, 0j]
    for g, dur in ((G, th_w / G), (0.0, t), (-G, th_r / G)):
        L = [[-gq, 0, 1j * g, -1j * g], [0, -gm, -1j * g, 1j * g],
             [1j * g, -1j * g, -Gam, 0], [-1j * g, 1j * g, 0, -Gam]]
        v = expv(L, v, dur)
        N = [[-eq, -1j * g], [-1j * g, -em]]
        a = expv(N, a, dur)
    return r_of(v[0].real, abs(a[0]))


def idle_cost(T1q, T2q, t):
    """Exact cost of leaving the excitation in the qubit for a time t (no pulse): p = e^{-gq t}, c = e^{-eq t}."""
    return r_of(math.exp(-t / T1q), math.exp(-t / T2q))


# ------------------------------------------------------------------ strong dephasing, no relaxation (G = 1)
# Closed forms of the paper (Prop. prop:strong and its text): the resonant pulse g = 1 with dephasing rates phi_q, phi_m
# has 1 - 2p = z(T), z = e^{-aT}[cosh(kT) + (a/k) sinh(kT)], k = sqrt(a^2 - 4), a = (phi_q + phi_m)/2, and the vacuum
# coherence c = e^{-aT} sinh(wT)/w, w = sqrt(d^2 - 1), d = |phi_q - phi_m|/2 (sin for d < 1, T e^{-aT} at d = 1).
# Everything is written with e^{-(a-k)T}-type factors only, so that no cosh/sinh overflows at long durations.

PHI_STAR_LO = '2.0941221534'      # certified enclosure of the equal-rate threshold phi_*/G (interval arithmetic in the
PHI_STAR_HI = '2.0941221542'      # paper's certificate); printed as text, never recomputed here


def res_zc(a, d, T):
    """(z, c) = (1 - 2 p_res, c_res) of the resonant pulse at G T = T (G = 1, no relaxation); a = Phi/2, d = |phi_q-phi_m|/2."""
    k2 = a * a - 4.0
    if k2 > 1e-12:
        k = math.sqrt(k2)
        e = math.exp(-2 * k * T)
        z = math.exp(-(a - k) * T) * ((1 + e) / 2 + (a / k) * (1 - e) / 2)
    elif k2 < -1e-12:
        k = math.sqrt(-k2)
        z = math.exp(-a * T) * (math.cos(k * T) + (a / k) * math.sin(k * T))
    else:
        z = math.exp(-a * T) * (1 + a * T)
    w2 = d * d - 1.0
    if w2 > 1e-12:
        w = math.sqrt(w2)
        c = math.exp(-(a - w) * T) * (1 - math.exp(-2 * w * T)) / (2 * w)
    elif w2 < -1e-12:
        w = math.sqrt(-w2)
        c = math.exp(-a * T) * math.sin(w * T) / w
    else:
        c = T * math.exp(-a * T)
    return z, c


def res_pc(phiq, phim, T):
    """(p_res, c_res, p + 2c - 1/2) of the resonant pulse at G T = T."""
    a, d = (phiq + phim) / 2, abs(phiq - phim) / 2
    z, c = res_zc(a, d, T)
    return (1 - z) / 2, c, (1 - z) / 2 + 2 * c - 0.5


def strong_logR_max(phiq, phim, Tmax=100.0, n=120):
    """max over 0 < T <= Tmax of log10(4c/(1-2p)) of the resonant pulse; +inf as soon as 1-2p <= 0 (p already above 1/2).
    R > 1 is the same as p + 2c > 1/2. Float, on a geometric grid of durations."""
    a, d = (phiq + phim) / 2, abs(phiq - phim) / 2
    best = -1e9
    for i in range(n):
        T = 0.02 * (Tmax / 0.02) ** (i / (n - 1))
        z, c = res_zc(a, d, T)
        if z <= 0:
            return float('inf')
        if c > 0:
            best = max(best, math.log10(4 * c / z))
    return best


def psuf_terms(delta):
    """The three terms of P_suf(delta) of Corollary cor:unequal (G = 1, 1 < delta < sqrt 5), exactly as defined there:
    s = artanh(Om/delta)/Om, L = log(2/Om)/s, Om = sqrt(delta^2-1); terms 16-8delta, 3+2 Om L+L^2, (delta^2/Om+L)^2-delta^2."""
    om = math.sqrt(delta * delta - 1.0)
    s = math.atanh(om / delta) / om
    L = math.log(2.0 / om) / s
    return (16 - 8 * delta, 3 + 2 * om * L + L * L, (delta * delta / om + L) ** 2 - delta * delta), om, s, L


def psuf(delta):
    return max(psuf_terms(delta)[0])
