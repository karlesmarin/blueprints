# encaje: núcleo del laboratorio del blueprint relay-floors (artículo II de qsl-hardware); Python PURO (Pyodide, sin
# numpy). Cota reforzada y recíproca de la Prop. 7.2 + Prop. 7.3 con PRIMITIVAS CERRADAS de las ventanas y del alcance
# (31-oct, tras V207: las tablas en ángulo daban hasta 7e-3 relativo cerca de v*) y rango adaptativo en T con colas
# rigurosas (V207: el mínimo podía quedar fuera de [0.05/G, 400/G]). Comprobado en prueba_lab.py, prueba_v207.py,
# prueba_metamorfica.py y prueba_receptor.py (mpmath, 30 dígitos).
"""The floor of a relay link qubit A -> bus mode C -> qubit B, for every pulse (Proposition 7.2 with the term f_A(T)^2
and reciprocity, Proposition 7.3, of "Quantum state transfer through a lossy bus").

Units: times in µs, couplings g/2π in MHz (G = 2π g in rad/µs). Each element is given by (T1, T2).

Closed forms. With R = √(G² + h²) and θ* = atan(h/G):
  emitter  ∫ sinφ dφ/(G sinφ + h cosφ)   = (c·u − s·ln sin u)/R,  u = φ + θ*   (c, s = cos θ*, sin θ*)
  receiver ∫ sinφ dφ/(G sinφ − h cosφ)   = (c·u + s·ln sin u)/R,  u = φ − θ*
  reach    ∫ cosφ dφ/(G cosφ − h sinφ)   = (c·v − s·ln cos v)/R,  v = φ + θ*
and the cos²φ-weighted windows are the same minus ∫ sin³φ/(R sin u), elementary in u (see _q_emit, _q_recv).
floor(...) returns (value, T, where) with where = 'interior', 'tail T→0' or 'tail T→∞' when the minimum is the
rigorous bound of a tail (the infimum is then approached, not attained in the explored range).
"""
import math

PI2 = math.pi / 2


def _bisect(f, lo, hi, it=80):
    """Root of an increasing f on [lo, hi] (f(lo) ≤ 0 ≤ f(hi))."""
    for _ in range(it):
        m = 0.5 * (lo + hi)
        if f(m) > 0:
            hi = m
        else:
            lo = m
    return 0.5 * (lo + hi)


class _Emitter:
    """Window of the emitter in the angle f = cos θ: t(θ) = ∫_0^θ sinφ dφ/(G sinφ + h cosφ), a(θ) = ∫_0^θ cos²φ (…)."""
    def __init__(self, G, d):
        self.G, self.h = G, d / 2
        if self.h == 0:
            return
        self.R = math.hypot(G, self.h)
        self.ts = math.atan2(self.h, G)
        self.c, self.s = math.cos(self.ts), math.sin(self.ts)
        self.t_end = self._t(PI2)

    def _t(self, th):
        u, u0 = th + self.ts, self.ts
        return (self.c * (u - u0) - self.s * (math.log(math.sin(u)) - math.log(math.sin(u0)))) / self.R

    def _q(self, u):
        c, s = self.c, self.s
        su, s2 = math.sin(u), math.sin(2 * u)
        return (c ** 3 * (u / 2 - s2 / 4) - 1.5 * c * c * s * su * su + 3 * c * s * s * (u / 2 + s2 / 4)
                - s ** 3 * (math.log(su) - su * su / 2))

    def _a(self, th):
        u, u0 = th + self.ts, self.ts
        return self._t(th) - (self._q(u) - self._q(u0)) / self.R

    def at(self, T):
        """(f_A(T), a_A(T))."""
        if self.h == 0:
            x = self.G * T
            return (math.cos(x), 0.0) if x < PI2 else (0.0, 0.0)
        if T >= self.t_end:
            return 0.0, self._a(PI2)
        th = _bisect(lambda x: self._t(x) - T, 0.0, PI2)
        return math.cos(th), self._a(th)


class _Receiver:
    """Receiver window run backwards from ζ = cos θ_ζ, and the reach M_B(T) = sin ψ(T)."""
    def __init__(self, G, d):
        self.G, self.h = G, d / 2
        if self.h == 0:
            self.vstar = 1.0
            return
        self.R = math.hypot(G, self.h)
        self.ts = math.atan2(self.h, G)
        self.c, self.s = math.cos(self.ts), math.sin(self.ts)
        self.vstar = math.cos(self.ts)

    # receiver: u = φ − θ*
    def _S(self, th):
        u = th - self.ts
        return (self.c * u + self.s * math.log(math.sin(u))) / self.R

    def _q(self, u):
        c, s = self.c, self.s
        su, s2 = math.sin(u), math.sin(2 * u)
        return (c ** 3 * (u / 2 - s2 / 4) + 1.5 * c * c * s * su * su + 3 * c * s * s * (u / 2 + s2 / 4)
                + s ** 3 * (math.log(su) - su * su / 2))

    def _B(self, th):
        return self._S(th) - self._q(th - self.ts) / self.R

    # reach: v = ψ + θ*,  τ(ψ) = (c (v − θ*) − s (ln cos v − ln cos θ*))/R
    def _tau(self, psi):
        v = psi + self.ts
        return (self.c * psi - self.s * (math.log(math.cos(v)) - math.log(math.cos(self.ts)))) / self.R

    def reach(self, T):
        if self.h == 0:
            x = self.G * T
            return math.sin(x) if x < PI2 else 1.0
        pmax = PI2 - self.ts                      # τ → ∞ there: M_B stays below v* = sin(pmax)
        lo, hi = 0.0, pmax * (1 - 1e-15)
        if self._tau(hi) <= T:
            return math.sin(hi)
        return math.sin(_bisect(lambda x: self._tau(x) - T, lo, hi))

    def window(self, zeta, T):
        """b_B(T, ζ) = ∫_0^T w_ζ² (0 without excess rate)."""
        if self.h == 0 or zeta <= 0:
            return 0.0
        x0 = math.acos(min(1.0, zeta))
        if x0 <= self.ts:                         # ζ ≥ v*: outside the reach; the trivial bound b ≥ 0
            return 0.0
        s0 = self._S(x0)
        if self._S(PI2) - s0 <= T:
            x1 = PI2
        else:
            x1 = _bisect(lambda x: self._S(x) - s0 - T, x0, PI2)
        return self._B(x1) - self._B(x0)


class Problem:
    """Amplitude problem with decay rates (rA, rC, rB) in 1/µs; GA, GB in rad/µs (emitter A, receiver B)."""
    def __init__(self, rA, rC, rB, GA, GB):
        self.r0 = min(rA, rC, rB)
        self.dA, self.dC, self.dB = rA - self.r0, rC - self.r0, rB - self.r0
        self.GB = GB
        self.em = _Emitter(GA, self.dA)
        self.rc = _Receiver(GB, self.dB)

    def amplitude(self, T):
        if T <= 0 or self.GB <= 0:
            return 0.0
        fA, aA = self.em.at(T)
        if self.dA == 0:
            aA = 0.0
        # V207 §5.3: expm1 avoids the cancellation 1 − e^{−d_B T} for tiny d_B
        JB = -math.expm1(-self.dB * T) / self.dB if self.dB > 0 else T
        MB = self.rc.reach(T)
        base = fA * fA + self.dA * aA
        kC = self.dC / (self.GB * self.GB * JB) if JB > 0 else 0.0

        def g(z):
            return z * z + base + self.dB * self.rc.window(z, T) + kC * z * z

        if g(0.0) > 1:
            return 0.0
        if g(MB) <= 1:
            z = MB
        else:
            lo, hi = 0.0, MB
            for _ in range(50):
                m = 0.5 * (lo + hi)
                if g(m) > 1:
                    hi = m
                else:
                    lo = m
            z = hi                                # V207 §5.4: the upper end, the safe side for an upper bound
        return math.exp(-self.r0 * T / 2) * z


def _golden(f, a, b, it=60):
    r = (math.sqrt(5) - 1) / 2
    c, d = b - r * (b - a), a + r * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(it):
        if fc < fd:
            b, d, fd = d, c, fc
            c = b - r * (b - a)
            fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + r * (b - a)
            fd = f(d)
    x = (a + b) / 2
    return x, f(x)


def link_bound(qa, bus, qb, ga_mhz, gb_mhz=None):
    """The function T -> lower bound on 1 - F_B at duration T (µs), for the link (both directions)."""
    gb_mhz = ga_mhz if gb_mhz is None else gb_mhz
    GA, GB = 2 * math.pi * ga_mhz, 2 * math.pi * gb_mhz
    dirs = (((qa, GA), (qb, GB)), ((qb, GB), (qa, GA)))
    pc = [Problem(2 / e[1], 2 / bus[1], 2 / r[1], ge, gr) for (e, ge), (r, gr) in dirs]
    pp = [Problem(1 / e[0], 1 / bus[0], 1 / r[0], ge, gr) for (e, ge), (r, gr) in dirs]

    def bound(T):
        c = min(p.amplitude(T) for p in pc)
        P = min(p.amplitude(T) for p in pp) ** 2
        return (1 - P) / 6 + (1 - c) / 3
    bound.problems = (pc, pp)
    return bound, min(GA, GB)


def floor(qa, bus, qb, ga_mhz, gb_mhz=None, grid=120, detail=False):
    """(floor on 1 - F_B, duration in µs that minimises the bound[, where]).

    The duration range grows until the minimum is interior (at most 8 decades each way); the two tails are closed by
    rigorous bounds: for T ≤ T_lo the amplitude is at most the reach M_B(T_lo) (non-decreasing in T), and for T ≥ T_hi
    at most e^{-r0 T_hi/2}. The floor is the smallest of the interior minimum and the two tail bounds."""
    bound, G = link_bound(qa, bus, qb, ga_mhz, gb_mhz)
    pc, pp = bound.problems
    rates = [1 / e[0] for e in (qa, bus, qb)] + [2 / e[1] for e in (qa, bus, qb)]
    lo = min(0.05 / G, 0.05 / max(rates))
    hi = max(400 / G, 20 / max(min(rates), 1e-300))
    per_dec = max(10, grid // 4)

    def scan(lo, hi):
        n = max(20, int(per_dec * math.log10(hi / lo)))
        ts = [lo * (hi / lo) ** (k / n) for k in range(n + 1)]
        return ts, [bound(t) for t in ts]

    ts, vs = scan(lo, hi)
    for _ in range(8):                                     # widen while the minimum sits on an end
        k = min(range(len(ts)), key=lambda i: vs[i])
        if k == 0 and lo > 1e-12 / G:
            lo /= 1e2
        elif k == len(ts) - 1 and hi < 1e12 / G:
            hi *= 1e2
        else:
            break
        ts, vs = scan(lo, hi)
    k = min(range(len(ts)), key=lambda i: vs[i])
    T, v = _golden(bound, ts[max(k - 1, 0)], ts[min(k + 1, len(ts) - 1)])
    if vs[k] < v:
        T, v = ts[k], vs[k]
    # rigorous tails
    c_lo = min(p.rc.reach(lo) for p in pc)
    P_lo = min(p.rc.reach(lo) for p in pp) ** 2
    tail_lo = (1 - P_lo) / 6 + (1 - c_lo) / 3
    tail_hi = (1 - math.exp(-pp[0].r0 * hi)) / 6 + (1 - math.exp(-pc[0].r0 * hi / 2)) / 3
    where = 'interior'
    if tail_lo < v:
        v, T, where = tail_lo, lo, 'tail T→0'
    if tail_hi < v:
        v, T, where = tail_hi, hi, 'tail T→∞'
    return (v, T, where) if detail else (v, T)
