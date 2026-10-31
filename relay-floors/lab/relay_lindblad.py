# encaje: laboratorio de relay-floors: ecuación maestra de Lindblad del relevo con tasas por elemento, Python puro
# (Pyodide); la misma que research/qsl-hardware/relevo/verificar_v203.error_min (comprobada en prueba_lab.py).
"""1 - F_B of a constant-coupling pulse A -> C -> B, with relaxation 1/T1 and Markovian pure dephasing
1/T2 - 1/(2 T1) on each element. F_B = (3 + P + 2c)/6 from one evolution of (|0> + |A>)/sqrt2: P = 2 rho_BB and
c = 2 |rho_B0| (Lemma 7.1 and Eq. (7.2) of the paper). Times in µs, couplings in rad/µs."""
import math


def _deriv(r, gA, gB, k1, gp):
    n = 4
    H = [[0.0] * n for _ in range(n)]
    H[1][2] = H[2][1] = gA
    H[2][3] = H[3][2] = gB
    d = [[0j] * n for _ in range(n)]
    for a in range(n):
        for b in range(n):
            s = 0j
            for c in range(n):
                s += H[a][c] * r[c][b] - r[a][c] * H[c][b]
            d[a][b] = -1j * s
    for j in (1, 2, 3):
        k = k1[j]
        d[0][0] += k * r[j][j]
        for a in range(n):
            if a != j:
                d[j][a] -= 0.5 * k * r[j][a] + gp[j] * r[j][a]
                d[a][j] -= 0.5 * k * r[a][j] + gp[j] * r[a][j]
        d[j][j] -= k * r[j][j]
    return d


def error_fb(T, gA, gB, qa, bus, qb, steps=400):
    """(1 - F_B, P, c) of the pulse g_A, g_B constant for a time T (µs)."""
    k1 = [0, 1 / qa[0], 1 / bus[0], 1 / qb[0]]
    gp = [0] + [1 / e[1] - 1 / (2 * e[0]) for e in (qa, bus, qb)]
    h = T / steps
    ad = lambda x, y, c: [[x[i][j] + c * y[i][j] for j in range(4)] for i in range(4)]
    r = [[0j] * 4 for _ in range(4)]
    r[0][0] = r[1][1] = r[0][1] = r[1][0] = 0.5
    for _ in range(steps):
        a = _deriv(r, gA, gB, k1, gp)
        b = _deriv(ad(r, a, h / 2), gA, gB, k1, gp)
        c = _deriv(ad(r, b, h / 2), gA, gB, k1, gp)
        e = _deriv(ad(r, c, h), gA, gB, k1, gp)
        r = [[r[i][j] + h / 6 * (a[i][j] + 2 * b[i][j] + 2 * c[i][j] + e[i][j]) for j in range(4)] for i in range(4)]
    P = 2 * r[3][3].real
    c = 2 * abs(r[3][0])
    return 1 - (3 + P + 2 * c) / 6, P, c


def evolve(couplings, T, qa, bus, qb, steps=400, samples=60):
    """Time-dependent couplings t -> (g_A, g_B) on [0, T] (µs). Returns (1 - F_B, trajectory), the trajectory being
    [(t, |a|, |c|, |b|)] with the moduli of the end state of the input |A> (populations of the superposition input × 2):
    the coordinates x, y, z of the paper, without the rescaling."""
    k1 = [0, 1 / qa[0], 1 / bus[0], 1 / qb[0]]
    gp = [0] + [1 / e[1] - 1 / (2 * e[0]) for e in (qa, bus, qb)]
    h = T / steps
    ad = lambda x, y, c: [[x[i][j] + c * y[i][j] for j in range(4)] for i in range(4)]
    r = [[0j] * 4 for _ in range(4)]
    r[0][0] = r[1][1] = r[0][1] = r[1][0] = 0.5
    every = max(1, steps // samples)
    point = lambda t, r: (t, math.sqrt(max(2 * r[1][1].real, 0)), math.sqrt(max(2 * r[2][2].real, 0)),
                          math.sqrt(max(2 * r[3][3].real, 0)))
    traj = [point(0.0, r)]
    for k in range(steps):
        t = k * h
        g0, gm, g1 = couplings(t), couplings(t + h / 2), couplings(t + h)
        a = _deriv(r, g0[0], g0[1], k1, gp)
        b = _deriv(ad(r, a, h / 2), gm[0], gm[1], k1, gp)
        c = _deriv(ad(r, b, h / 2), gm[0], gm[1], k1, gp)
        e = _deriv(ad(r, c, h), g1[0], g1[1], k1, gp)
        r = [[r[i][j] + h / 6 * (a[i][j] + 2 * b[i][j] + 2 * c[i][j] + e[i][j]) for j in range(4)] for i in range(4)]
        if (k + 1) % every == 0 or k == steps - 1:
            traj.append(point(t + h, r))
    P = 2 * r[3][3].real
    c = 2 * abs(r[3][0])
    return 1 - (3 + P + 2 * c) / 6, traj


def pulse_minimal(G):
    """g_A = g_B = G for π/(√2 G)."""
    return (lambda t: (G, G)), math.pi / (math.sqrt(2) * G)


def pulse_sequential(G):
    """Two swaps: A -> bus with g_A = G for π/(2G), then bus -> B with g_B = G."""
    t1 = math.pi / (2 * G)
    return (lambda t: (G, 0.0) if t < t1 else (0.0, G)), 2 * t1


def pulse_adiabatic(G, T):
    """Counter-intuitive (STIRAP-like) pulse of duration T within the box: g_A = G sin θ, g_B = G cos θ, with
    θ = (π/2)(3s² − 2s³), s = t/T. The dark state cos θ |A> − sin θ |B> goes from A to B; the longer T, the less the
    bus is visited (and the longer the qubits decay)."""
    def g(t):
        s = min(max(t / T, 0.0), 1.0)
        th = math.pi / 2 * (3 * s * s - 2 * s * s * s)
        return G * math.sin(th), G * math.cos(th)
    return g, T


def minimal_time_error(qa, bus, qb, g_mhz, steps=400):
    """The simultaneous pulse g_A = g_B = G for pi/(sqrt2 G), the fastest complete transfer with one mode."""
    G = 2 * math.pi * g_mhz
    T = math.pi / (math.sqrt(2) * G)
    return error_fb(T, G, G, qa, bus, qb, steps)[0], T
