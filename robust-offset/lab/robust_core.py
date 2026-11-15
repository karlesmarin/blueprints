# encaje: núcleo de cálculo de los laboratorios del blueprint robust-offset (paper B): dinámica exacta de dos niveles,
# familias de pulsos, longitud de Dubins y mínimos sobre la familia giro-espera-giro; Python puro (Pyodide), sin numpy.
"""Core of the labs of «Robust qubit–memory transfer against quasi-static frequency noise costs time and exposure».

Two unit systems, as in the paper's scripts:

- G = 1 (z0 = 1/2, A0 = pi/4, T0 = pi/2): the exact dynamics (``evolve``), the theorem's margins, the cost lab;
- G = 1/2 (z0 = 1, A0 = pi/2, T0 = pi): the planar family C_{pi+phi} S C_phi, whose exposures (x, y) = (A - A0, B - A0)
  and leakage z = |zeta|/z0 are  x = phi - sin phi + w (1 - cos phi)/2,  y = phi + sin phi + w (1 + cos phi)/2,
  z = cos phi - w sin phi/2  (rem:planar; w is the wait in G = 1/2 units). Only ratios matter there.

``min_family`` minimises any g(z, x, y) over the family (and its mirror x <-> y): g is a polynomial of degree 2 in w, so
the minimum over w is closed-form and only phi is searched (grid + golden section). This is NUMERICAL: the certificates
(interval arithmetic) are in the paper."""
import cmath
import math

A0H = math.pi / 2          # A0 in G = 1/2 units
TOL = 1e-10                # a minimum below -TOL counts as «the competitor wins»


# ---------------------------------------------------------------- exact two-level dynamics (G = 1 units elsewhere)
def _mul(p, q):
    return (p[0] * q[0] + p[1] * q[2], p[0] * q[1] + p[1] * q[3], p[2] * q[0] + p[3] * q[2], p[2] * q[1] + p[3] * q[3])


def _dag(p):
    return (p[0].conjugate(), p[2].conjugate(), p[1].conjugate(), p[3].conjugate())


def segment(U0, g, D, h):
    """One piece with H = [[D, g], [conj g, 0]] (|a> = qubit) lasting h, exactly. Returns (U, K, n) with
    K = int_0^h U^dag P_a U dt = (h/2) I + (1/2) sum_i n_i sigma_i  (so n is the integral of the Bloch vector of the
    Heisenberg-evolved projector over the piece) and U the evolution after the piece."""
    hx, hy, hz = g.real, -g.imag, D / 2.0
    R = math.sqrt(hx * hx + hy * hy + hz * hz)
    if R < 1e-15:
        ph = cmath.exp(-0.5j * D * h)
        U = _mul((ph, 0j, 0j, ph), U0)
        u = (0.0, 0.0, h)                              # no rotation: v(s) = e_z
    else:
        mx, my, mz = hx / R, hy / R, hz / R
        c, s = math.cos(R * h), math.sin(R * h)
        ph = cmath.exp(-0.5j * D * h)
        a = ph * (c - 1j * s * mz)
        b = ph * (-1j * s * (mx - 1j * my))
        cc = ph * (-1j * s * (mx + 1j * my))
        d = ph * (c + 1j * s * mz)
        U = _mul((a, b, cc, d), U0)
        th = 2 * R * h
        s1, s2 = math.sin(th) / (2 * R), (1 - math.cos(th)) / (2 * R)
        cx, cy, cz = my * 1.0, -mx, 0.0               # m x e_z = (my, -mx, 0)
        k = mz * (h - s1)
        u = (-cx * s2 + k * mx, -cy * s2 + k * my, s1 - cz * s2 + k * mz)
    # K_loc = h/2 I + (1/2) u.sigma, conjugated by U0: K = U0^dag K_loc U0
    ux, uy, uz = u
    kl = (h / 2 + uz / 2, (ux - 1j * uy) / 2, (ux + 1j * uy) / 2, h / 2 - uz / 2)
    K = _mul(_mul(_dag(U0), kl), U0)
    n = (2 * K[1].real, -2 * K[1].imag, K[0].real - K[3].real)   # tr(sigma_x K), tr(sigma_y K), tr(sigma_z K)
    return U, K, n


def evolve(pieces, steps=0):
    """pieces = [(g, D, h)] -> dict(A, B, z (|zeta|), T, trans (|U_aa|)), and, if steps > 0, the curve r(t) = int n
    sampled ``steps`` times per piece (list of [rx, ry, rz])."""
    U = (1 + 0j, 0j, 0j, 1 + 0j)
    A = B = T = 0.0
    z = 0j
    r = [0.0, 0.0, 0.0]
    path = [list(r)]
    for g, D, h in pieces:
        if h <= 0:
            continue
        if steps:
            for j in range(1, steps + 1):
                _, _, nj = segment(U, g, D, h * j / steps)
                path.append([r[0] + nj[0], r[1] + nj[1], r[2] + nj[2]])
        U2, K, n = segment(U, g, D, h)
        A += K[0].real
        B += K[3].real
        z += K[2]
        T += h
        r = [r[0] + n[0], r[1] + n[1], r[2] + n[2]]
        U = U2
    out = dict(A=A, B=B, z=abs(z), T=T, trans=abs(U[0]))
    if steps:
        out['path'] = path
    return out


def pieces_bang_bang(d, rev=False):
    p = [(1 + 0j, 0.0, (math.pi + d) / 2), (-1 + 0j, 0.0, d / 2)]
    return p[::-1] if rev else p


def pieces_twt(alpha, w):
    """The pulse of Theorem (a): +G during alpha/2, nothing during w, +G during (pi - alpha)/2 (G = 1)."""
    return [(1 + 0j, 0.0, alpha / 2), (0j, 0.0, w), (1 + 0j, 0.0, (math.pi - alpha) / 2)]


def pieces_back(phi, w):
    """C_{pi+phi} S C_phi: a turn of pi + phi at +G, a wait w, a turn of phi back at -G (G = 1)."""
    return [(1 + 0j, 0.0, (math.pi + phi) / 2), (0j, 0.0, w), (-1 + 0j, 0.0, phi / 2)]


Z0, A0, T0 = 0.5, math.pi / 4, math.pi / 2           # G = 1


def margins(c, G=1.0):
    """(a) min(A - A0, B - A0, (A-A0)(B-A0) - (|zeta| - z0)^2) and (b) T - T0 - arccos(|zeta|/z0)/G if |zeta| <= z0, else
    T - T0 - 2(|zeta| - z0): the pulse satisfies the theorem iff both are >= 0."""
    z0, a0, t0 = 1 / (2 * G), math.pi / (4 * G), math.pi / (2 * G)
    ma = min(c['A'] - a0, c['B'] - a0, (c['A'] - a0) * (c['B'] - a0) - (c['z'] - z0) ** 2)
    if c['z'] <= z0:
        mb = c['T'] - t0 - math.acos(min(1.0, c['z'] / z0)) / G
    else:
        mb = c['T'] - t0 - 2 * (c['z'] - z0)
    return ma, mb


# ---------------------------------------------------------------- random complete transfers with |g| <= umax G
def random_pulse(rng, k, umax=1.0, dmax=3.0):
    """k pieces with complex g (|g| <= umax) and detuning |D| <= dmax; the first k-1 are random, the last one is built
    so that the state ends exactly at |b> (its rotation axis is orthogonal to s + e_z, the angle is read off the
    geometry), and the result is verified: |U_aa| < 1e-9 or the pulse is rejected. Returns the pieces or None."""
    for _ in range(200):
        pieces, U = [], (1 + 0j, 0j, 0j, 1 + 0j)
        for _j in range(max(k - 1, 0)):
            amp = umax * math.sqrt(rng.random())
            g = amp * cmath.exp(1j * rng.uniform(-math.pi, math.pi))
            D = rng.uniform(-dmax, dmax) * rng.choice([0, 0.5, 1]) if dmax > 0 else 0.0
            h = rng.uniform(0.1, 1.6)
            pieces.append((g, D, h))
            U = segment(U, g, D, h)[0]
        a, b = U[0], U[2]                                # state U|a>
        s = (2 * (a.conjugate() * b).real, 2 * (a.conjugate() * b).imag, abs(a) ** 2 - abs(b) ** 2)
        w = (s[0], s[1], s[2] + 1)
        nw = math.sqrt(sum(v * v for v in w))
        if nw < 1e-9:
            return pieces                                # already at the memory
        wh = [v / nw for v in w]
        if dmax > 0:
            v = [rng.gauss(0, 1) for _ in range(3)]
        else:
            sg = rng.choice([-1, 1])
            v = [-wh[1] * sg, wh[0] * sg, 0.0]           # e_z x w direction (m_z = 0): the axis without detuning
        dot = sum(v[i] * wh[i] for i in range(3))
        m = [v[i] - dot * wh[i] for i in range(3)]
        nm = math.sqrt(sum(x * x for x in m))
        if nm < 1e-9:
            continue
        m = [x / nm for x in m]
        if dmax == 0:
            m[2] = 0.0
            nm = math.hypot(m[0], m[1])
            if nm < 1e-9:
                continue
            m = [m[0] / nm, m[1] / nm, 0.0]
        hor = math.hypot(m[0], m[1])
        if hor < 1e-6:
            continue
        t = (0.0, 0.0, -1.0)
        ms, mt = sum(m[i] * s[i] for i in range(3)), -m[2]
        sp = [s[i] - ms * m[i] for i in range(3)]
        tp = [t[i] - mt * m[i] for i in range(3)]
        n2 = sum(x * x for x in sp)
        if n2 < 1e-12:
            continue
        cross = (sp[1] * tp[2] - sp[2] * tp[1], sp[2] * tp[0] - sp[0] * tp[2], sp[0] * tp[1] - sp[1] * tp[0])
        th = math.atan2(sum(m[i] * cross[i] for i in range(3)), sum(sp[i] * tp[i] for i in range(3)))
        Rmax = umax / hor
        if dmax > 0 and abs(m[2]) > 1e-9:
            Rmax = min(Rmax, dmax / (2 * abs(m[2])))
        for R in (Rmax * rng.uniform(0.3, 1.0), Rmax):
            for ang in (th % (2 * math.pi), (-th) % (2 * math.pi)):
                g = R * (m[0] - 1j * m[1])
                last = (g, 2 * R * m[2], ang / (2 * R))
                if last[2] <= 0:
                    continue
                if abs(g) > umax + 1e-12:
                    continue
                c = evolve(pieces + [last])
                if c['trans'] < 1e-9:
                    return pieces + [last]
    return None


# ---------------------------------------------------------------- Dubins U-turn (cost lab), z0 = 1 units
def dubins_L(s):
    """Length (in units of z0) of the shortest planar U-turn back to its axis with axial displacement s: the least of
    the candidates LSL/RSR, LSR/RSL (|s| >= 2) and the CCC pairs (s^2 <= 12) listed in the text of prop:cost."""
    s = abs(s)
    c = [3 * math.pi + math.sqrt(4 + s * s)]
    if s >= 2:
        r = math.sqrt(s * s - 4)
        c.append(2 * math.pi - 2 * math.atan(r / 2) + r)
    if s * s <= 12:
        q = math.asin(math.sqrt(4 + s * s) / 4)
        if s <= 2:
            c += [3 * math.pi - 4 * q, 3 * math.pi + 4 * q]
        else:
            c += [5 * math.pi - 4 * q, math.pi + 4 * q]
    return min(c)


def dubins_L_closed(s):
    """The closed form L(s) printed in the paper (prop:cost)."""
    a = abs(s)
    if a <= 2:
        return 3 * math.pi - 4 * math.asin(math.sqrt(4 + s * s) / 4)
    r = math.sqrt(s * s - 4)
    return 2 * math.pi - 2 * math.atan(r / 2) + r


def golden(f, lo, hi, it=70):
    g = (math.sqrt(5) - 1) / 2
    a, b = lo, hi
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(it):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a)
            fd = f(d)
    x = (a + b) / 2
    return x, f(x)


# ---------------------------------------------------------------- the planar family (G = 1/2 units)
def fam(phi, w):
    """(z, x, y) of C_{pi+phi} S C_phi: z = |zeta|/z0, x = A - A0, y = B - A0 (units G = 1/2)."""
    s, c = math.sin(phi), math.cos(phi)
    return c - w * s / 2, phi - s + w * (1 - c) / 2, phi + s + w * (1 + c) / 2


def _min_over_w(g, phi, mirror):
    """min over w in [0, 2 cot(phi)] (z >= 0) of g(z, x, y): g is quadratic in w. Returns (value, w)."""
    def at(w):
        z, x, y = fam(phi, w)
        return g(z, y, x) if mirror else g(z, x, y)
    s = math.sin(phi)
    wmax = 2 * math.cos(phi) / s if s > 1e-12 else 1e9
    g0, g1, g2 = at(0.0), at(1.0), at(2.0)
    a = (g2 - 2 * g1 + g0) / 2
    b = g1 - g0 - a
    cands = [0.0, wmax]
    if a > 1e-300:
        cands.append(min(max(-b / (2 * a), 0.0), wmax))
    best = min(cands, key=lambda w: g0 + b * w + a * w * w)
    return at(best), best


def min_family(g, mirror=False, ngrid=140, both=False):
    """Minimum of g(z, x, y) over the family (and, with ``both``, over its mirror too). Returns a dict with the value
    (0 means the square pulse, phi -> 0), phi, w, z, x, y of the minimiser. NUMERICAL (grid + golden section)."""
    best = dict(value=0.0, phi=0.0, w=0.0, z=1.0, x=0.0, y=0.0, mirror=False)
    for mir in ((False, True) if both else (mirror,)):
        f = lambda p: _min_over_w(g, p, mir)[0]
        ps = [A0H * (i + 0.5) / ngrid for i in range(ngrid)] + [A0H]
        vs = [f(p) for p in ps]
        for i in range(len(ps)):
            lo = vs[i - 1] if i > 0 else float('inf')
            hi = vs[i + 1] if i < len(ps) - 1 else float('inf')
            if vs[i] <= lo and vs[i] <= hi:
                a = ps[i - 1] if i > 0 else max(ps[0] * 0.01, 1e-9)
                b = ps[i + 1] if i < len(ps) - 1 else ps[i]
                p, v = golden(f, a, b)
                if v < best['value']:
                    w = _min_over_w(g, p, mir)[1]
                    z, x, y = fam(p, w)
                    best = dict(value=v, phi=p, w=w, z=z, x=x, y=y, mirror=mir)
    return best


# ---------------------------------------------------------------- correlated offsets (rem:corr), G = 1/2, sigma_q^2 = 1
def g_corr(rho, kappa):
    C = kappa * math.sqrt(rho)
    V = 1 + rho - 2 * C

    def g(z, x, y):
        return 2 * V * (z * z - 1) + x * (2 * A0H + x) + 2 * C * (A0H * (x + y) + x * y) + rho * y * (2 * A0H + y)
    return g


def six_J_square(rho, kappa):
    C = kappa * math.sqrt(rho)
    return 2 * (1 + rho - 2 * C) + A0H ** 2 * (1 + 2 * C + rho)


def rho_c(kappa, lo=1e-4, hi=1.0, iters=44, ngrid=110):
    """Crossing of the family with the square pulse: the least rho with min g >= 0, by bisection on the sign of
    min g (competitor wins for rho < rho_c). Mode: the family (x small); rho <= 1."""
    for _ in range(iters):
        mid = math.sqrt(lo * hi)
        if min_family(g_corr(mid, kappa), ngrid=ngrid)['value'] < -TOL:
            lo = mid
        else:
            hi = mid
    return math.sqrt(lo * hi)


def rho_sufficient(kappa):
    """Lower end of the set of rho (sigma_q^2 = 1, sigma_m^2 = rho) where (pi/2) sqrt((1 + C)(rho + C)) >= V, with
    C = kappa sqrt(rho), V = 1 + rho - 2 C (rem:corr's sufficient condition); None if it never holds below rho = 1."""
    def ok(rho):
        C = kappa * math.sqrt(rho)
        return (math.pi / 2) * math.sqrt((1 + C) * (rho + C)) >= 1 + rho - 2 * C
    if not ok(1.0):
        return None
    lo, hi = 1e-9, 1.0
    if ok(lo):
        return lo
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def kappa_c_square():
    return (4 - math.pi) / (4 + math.pi)


# ---------------------------------------------------------------- qubit and memory losses (prop:noiseloss), G = 1/2
def q_fun(z, x):
    return 2 * (z * z - 1) + x * (2 * A0H + x)


def g_loss(lam, r):
    """12 (J - J_sq) = Lam Q + 4 (y + r x) in units G = 1/2, gamma_m = 1, sigma_q^2 = Lam/2, r = gamma_q/gamma_m."""
    def g(z, x, y):
        return lam * q_fun(z, x) + 4 * (y + r * x)
    return g


def suficiente(r):
    return (math.pi + math.sqrt(math.pi ** 2 + 16 * r)) / 2


def lambda_c(r, ngrid=140, iters=60):
    """Lambda_c(r): the family's crossing with the square pulse. g = Lam Q + 4(y + r x) is linear in Lam, so
    Lam_c = min over the family of 4(y + r x)/(-Q) (Q < 0): found by Dinkelbach iterations (minimise g at the current
    Lam, set Lam to the ratio at the minimiser) from above the crossing. Returns (Lam_c, phi, w, z)."""
    lam = suficiente(r) + 8.0
    for _ in range(12):
        m = min_family(g_loss(lam, r), both=True, ngrid=ngrid)
        if m['value'] < -TOL:
            break
        lam *= 1.5
    best = None
    for _ in range(iters):
        m = min_family(g_loss(lam, r), both=True, ngrid=ngrid)
        z, x, y = m['z'], (m['y'] if m['mirror'] else m['x']), (m['x'] if m['mirror'] else m['y'])
        q = q_fun(z, x)
        if m['value'] >= -TOL or q >= 0:
            break
        new = 4 * (y + r * x) / (-q)
        best = (new, m['phi'], m['w'], z, m['mirror'])
        if abs(new - lam) < 1e-13 * max(1.0, lam):
            lam = new
            break
        lam = new
    return best


def J_sq_rel(lam, r):
    """12 J_sq in the same units (so that the relative excess of a pulse is g/(12 J_sq))."""
    return lam * (2 + A0H ** 2) + 4 * (1 + r) * A0H
