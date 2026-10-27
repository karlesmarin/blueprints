# encaje: cruce de formulas con Magesan & Gambetta 2020 (PRA 101, 052308, arXiv:1804.04073) sobre 1212 CX de IBM (qsl-hardware)
# Reproduce primero el 1.109 de cruce_formulas.py (orden 1), luego eq. (4.25) (orden 3 en Omega), el limite qubit (3.14)
# y una diagonalizacion en bloques de minima accion (Sec. A1) numerica. Controles de signo erroneo al final.
import json
from pathlib import Path
import numpy as np

RAIZ = Path(__file__).resolve().parent.parent / "datos_pulsos"
PI2 = np.pi / 2


def shape(dur, sigma, width=0):
    # Qiskit lifted Gaussian / GaussianSquare, muestras con pico 1 (igual que cruce_formulas.area_lift)
    t = np.arange(dur) + 0.5
    if width:
        rf = (dur - width) / 2
        c1, c2 = rf, rf + width
        g = np.where(t < c1, np.exp(-((t - c1) ** 2) / (2 * sigma ** 2)),
                     np.where(t > c2, np.exp(-((t - c2) ** 2) / (2 * sigma ** 2)), 1.0))
        g0 = np.exp(-((rf + 0.5) ** 2) / (2 * sigma ** 2))
    else:
        c = dur / 2
        g = np.exp(-((t - c) ** 2) / (2 * sigma ** 2))
        g0 = np.exp(-((c + 0.5) ** 2) / (2 * sigma ** 2))
    return (g - g0) / (1 - g0)


def amp_abs(a):
    return abs(complex(*a)) if isinstance(a, list) else abs(a)


# ---- formulas de Magesan & Gambetta (coef. de ZX/2, es decir H = (c/2) Z x X) ----
def c_first(J, Om, D, d):          # eq. (4.26)
    return -(J * Om / D) * d / (d + D)


def c_third(J, Om, D, d):          # eq. (4.25) = (4.26) + termino en Omega^3
    extra = J * Om ** 3 * d ** 2 * (3 * d ** 3 + 11 * d ** 2 * D + 15 * d * D ** 2 + 9 * D ** 3) / (
        2 * D ** 3 * (d + D) ** 3 * (d + 2 * D) * (3 * d + 2 * D))
    return c_first(J, Om, D, d) + extra


def c_qubit(J, Om, D, d):          # eq. (3.14), d -> infinito
    return -J * Om / np.sqrt(D ** 2 + Om ** 2)


# ---- diagonalizacion en bloques de minima accion (Sec. A1, Cederbaum et al.) ----
NL = 4


def _ops():
    b = np.diag(np.sqrt(np.arange(1, NL)), 1)
    I = np.eye(NL)
    return np.kron(b, I), np.kron(I, b)


B1, B2 = _ops()
N1, N2 = B1.T @ B1, B2.T @ B2
ID = np.eye(NL * NL)


def idx(a, c):
    return a * NL + c


def c_bd(J, Om, D, d1, d2):
    H0 = (D * N1 + d1 / 2 * N1 @ (N1 - ID) + d2 / 2 * N2 @ (N2 - ID) + J * (B1.T @ B2 + B2.T @ B1))
    E0, U0 = np.linalg.eigh(H0)
    lab = {}
    for key in ((0, 0), (0, 1), (1, 0), (1, 1)):
        k = np.argmax(np.abs(U0[idx(*key), :]))
        lab[key] = (E0[k], U0[:, k] * np.sign(U0[idx(*key), k]))
    wd = (lab[(1, 1)][0] - lab[(1, 0)][0] + lab[(0, 1)][0] - lab[(0, 0)][0]) / 2     # eq. (4.10)
    H = H0 - wd * (N1 + N2) + Om / 2 * (B1 + B1.T)
    E, X = np.linalg.eigh(H)
    Q = np.column_stack([lab[(0, 0)][1], lab[(0, 1)][1], lab[(1, 0)][1], lab[(1, 1)][1]])
    Qr = np.linalg.svd(ID - Q @ Q.T)[0][:, : NL * NL - 4]
    Xd = np.column_stack([Q, Qr]).T @ X
    blocks = [[0, 1], [2, 3], list(range(4, NL * NL))]
    w = np.array([[np.sum(Xd[bl, j] ** 2) for bl in blocks] for j in range(NL * NL)])
    asg = np.argmax(w, axis=1)
    if [int(np.sum(asg == i)) for i in range(3)] != [2, 2, NL * NL - 4]:
        return np.nan
    Hs = []
    for i in (0, 1):
        cols = np.where(asg == i)[0]
        u, s, vh = np.linalg.svd(Xd[np.ix_(blocks[i], cols)])
        Fk = u @ vh
        Hs.append(Fk @ np.diag(E[cols]) @ Fk.T)
    return Hs[0][0, 1] - Hs[1][0, 1]      # H[1,2] - H[3,4] = coef. de ZX/2 (ver informe)


# ---- lectura de los datos (idem cruce_formulas.py) ----
gates = []
for b in sorted(RAIZ.iterdir()):
    fd, fc = b / f"defs_{b.name}.json", b / f"conf_{b.name}.json"
    if not (fd.exists() and fc.exists()):
        continue
    d = json.loads(fd.read_text())
    c = json.loads(fc.read_text())
    v = (c.get("hamiltonian") or {}).get("vars", {})
    if "omegad0" not in v:
        continue
    dt = c["dt"] * (1e9 if c["dt"] < 1e-6 else 1)
    ulo = c.get("u_channel_lo", [])
    ctrl_of = {}
    for name, info in (c.get("channels") or {}).items():
        if name.startswith("u") and info.get("operates", {}).get("qubits"):
            ctrl_of[int(name[1:])] = info["operates"]["qubits"][0]
    for cmd in d.get("cmd_def", []):
        if cmd["name"] != "cx":
            continue
        cr = [s for s in cmd["sequence"] if s.get("ch", "").startswith("u") and s.get("name") == "parametric_pulse"
              and s.get("pulse_shape") == "gaussian_square"]
        if len(cr) < 2:
            continue
        k = int(cr[0]["ch"][1:])
        if k not in ctrl_of or k >= len(ulo):
            continue
        cq, tq = ctrl_of[k], ulo[k][0]["q"]
        J = v.get(f"jq{min(cq, tq)}q{max(cq, tq)}")
        if not J:
            continue
        P = cr[0]["parameters"]
        g = np.concatenate([shape(s["parameters"]["duration"], s["parameters"]["sigma"], s["parameters"]["width"])
                            for s in cr])
        gates.append(dict(k=k, bk=b.name, cq=cq, tq=tq, J=J, Om=amp_abs(P["amp"]) * v[f"omegad{cq}"],
                          D=v[f"wq{cq}"] - v[f"wq{tq}"], d1=v[f"delta{cq}"], d2=v[f"delta{tq}"], g=g, dt=dt))


print(f"CX con CR: {len(gates)} puertas en {len({x[chr(98) + chr(107)] for x in gates})} backends (datos_pulsos)")


def theta(fn, x, D=None, d=None):
    D = x["D"] if D is None else D
    d = x["d1"] if d is None else d
    return float(np.sum(fn(x["J"], x["Om"] * x["g"], D, d)) * x["dt"])


def stats(name, r, extra=""):
    r = np.asarray(r)
    ok = np.isfinite(r)
    q = r[ok]
    p10, med, p90 = np.percentile(q, [10, 50, 90])
    print(f"{name:34s} n={ok.sum():4d} mediana {med:6.3f}  [p10 {p10:6.3f}, p90 {p90:6.3f}]  (p90-p10)/med {(p90 - p10) / med:5.2f}"
          f"  sd(ln) {np.std(np.log(q)):5.2f}  en [0.8,1.2]: {np.mean((q > 0.8) & (q < 1.2)):4.0%} {extra}")
    return med


r1 = np.array([abs(theta(c_first, x)) / PI2 for x in gates])
print()
print("=== CONTROL 1: orden 1, eq. (4.26) (debe reproducir 1.109 [0.870, 1.472]) ===")
m1 = stats("orden 1", r1)
ok1 = abs(m1 - 1.109) < 0.0015 and abs(np.percentile(r1, 10) - 0.870) < 0.0015 and abs(np.percentile(r1, 90) - 1.472) < 0.0015
print("   " + ("OK: reproduce 1.109 / 0.870 / 1.472" if ok1 else "FALLO: NO reproduce 1.109 -> PARAR"))
if not ok1:
    raise SystemExit(1)

r3 = np.array([abs(theta(c_third, x)) / PI2 for x in gates])
rq = np.array([abs(theta(c_qubit, x)) / PI2 for x in gates])
print()
print("=== RESULTADO: eq. (4.25) (orden 3 en Omega), integrada sobre la forma del pulso ===")
stats("orden 3 (4.25)", r3)
stats("limite qubit (3.14)", rq)
OD = np.array([abs(x["Om"] / x["D"]) for x in gates])
Dd = np.array([x["D"] / abs(x["d1"]) for x in gates])
print(f"   |Om/D| mediana {np.median(OD):.3f}; fraccion Om/D>0.3: {np.mean(OD > 0.3):.0%}; D/|delta| en [{Dd.min():.2f},{Dd.max():.2f}], D>0: {np.mean(Dd > 0):.0%}")
corr = np.array([theta(c_third, x) / theta(c_first, x) - 1 for x in gates])
print(f"   correccion relativa (3o/1o - 1): mediana {np.median(corr):+.3f}, p10 {np.percentile(corr, 10):+.3f}, p90 {np.percentile(corr, 90):+.3f}")
print(f"   fraccion con correccion NEGATIVA: {np.mean(corr < 0):.0%}")
dist = np.array([min(abs(x["D"] - p * (-x["d1"])) / abs(x["d1"]) for p in (0.5, 1.0, 1.5)) for x in gates])
print(f"   cerca de un polo (|D - p|delta|| < 0.15|delta|, p=0.5,1,1.5): {np.mean(dist < 0.15):.0%}")
lejos = dist >= 0.15
weak = OD < 0.3
print()
print("--- subconjuntos ---")
stats("orden 1, lejos de polos", r1[lejos])
stats("orden 3, lejos de polos", r3[lejos])
stats("orden 1, lejos y Om/D<0.3", r1[lejos & weak])
stats("orden 3, lejos y Om/D<0.3", r3[lejos & weak])
print(f"   (n lejos y Om/D<0.3: {int(np.sum(lejos & weak))})")

print()
print("=== diagonalizacion en bloques de minima accion, numerica (Sec. A1; NL=4 niveles) ===")
for Om in (0.001, 0.02, 0.05):
    print(f"   parametros Sheldon, Om={Om:5.3f}: BD {c_bd(3.8e-3, Om, 0.2, -0.33, -0.33):+.6f}  (4.26) {c_first(3.8e-3, Om, 0.2, -0.33):+.6f}"
          f"  (4.25) {c_third(3.8e-3, Om, 0.2, -0.33):+.6f}  qubit {c_qubit(3.8e-3, Om, 0.2, -0.33):+.6f}")
SG = np.linspace(0, 1, 13)
rb = []
for x in gates:
    cs = np.array([0.0] + [c_bd(x["J"], s * x["Om"], x["D"], x["d1"], x["d2"]) for s in SG[1:]])
    if not np.all(np.isfinite(cs)):
        rb.append(np.nan)
        continue
    rb.append(abs(float(np.sum(np.interp(x["g"], SG, cs)) * x["dt"])) / PI2)
rb = np.array(rb)
okb = np.isfinite(rb)
print(f"   BD no convergente/ambigua en {int(np.sum(~okb))} puertas")
stats("BD numerica", rb)
stats("  orden 1, mismas puertas", r1[okb])
stats("  orden 3, mismas puertas", r3[okb])
stats("  BD, lejos de polos", rb[okb & lejos])

print()
print("=== CONTROLES DE SIGNO ERRONEO (deben alejar la mediana de 1) ===")
stats("orden 1 con D -> -D", [abs(theta(c_first, x, D=-x["D"])) / PI2 for x in gates])
stats("orden 1 con delta -> -delta", [abs(theta(c_first, x, d=-x["d1"])) / PI2 for x in gates])
stats("orden 3 con D -> -D", [abs(theta(c_third, x, D=-x["D"])) / PI2 for x in gates])


print()
print("=== distribucion de parametros y subconjunto Omega/2pi < 50 MHz (limite citado por Magesan-Gambetta, Sec. IV) ===")
om = np.array([x["Om"] for x in gates]) / (2 * np.pi) * 1000
print("   Omega/2pi (MHz) p10/50/90:", np.round(np.percentile(om, [10, 50, 90]), 1), " fraccion > 50 MHz:", f"{np.mean(om > 50):.0%}")
print("   J/2pi (MHz) p10/50/90:", np.round(np.percentile([x["J"] for x in gates], [10, 50, 90]) / (2 * np.pi) * 1000, 2))
print("   Delta/2pi (MHz) p10/50/90:", np.round(np.percentile([x["D"] for x in gates], [10, 50, 90]) / (2 * np.pi) * 1000, 0))
print("   delta_c/2pi (MHz) p10/50/90:", np.round(np.percentile([x["d1"] for x in gates], [10, 50, 90]) / (2 * np.pi) * 1000, 0))
sel = om < 50
print("   n con Omega<50 MHz:", int(sel.sum()))
stats("orden 1, Omega<50", r1[sel])
stats("orden 3, Omega<50", r3[sel])
stats("BD, Omega<50", rb[sel])
stats("orden 1, Omega<50, lejos de polos", r1[sel & lejos])
stats("orden 3, Omega<50, lejos de polos", r3[sel & lejos])
stats("BD, Omega<50, lejos de polos", rb[sel & lejos])


print()
print("=== SENSIBILIDAD: coeficiente omegad del h_str del canal U (p. ej. omegad1*X0||U0) frente a omegad del control ===")
conf_cache = {}
for x in gates:
    if x["bk"] not in conf_cache:
        cc = json.loads((RAIZ / x["bk"] / f"conf_{x[chr(98) + chr(107)]}.json").read_text())
        hm = {}
        for s in cc["hamiltonian"]["h_str"]:
            if "{" in s or "||U" not in s:
                continue
            lhs, rhs = s.split("*")[0], s.split("*")[1]
            hm[int(rhs.split("||U")[1])] = (int(lhs[6:]), int(rhs.split("||")[0][1:]))
        conf_cache[x["bk"]] = (hm, cc["hamiltonian"]["vars"])
nmis = 0
nop = 0
r1b, r3b = [], []
for x in gates:
    hm, vv = conf_cache[x["bk"]]
    a, bq = hm[x["k"]]
    nmis += int(a != x["cq"])
    nop += int(bq != x["cq"])
    f = vv[f"omegad{a}"] / vv[f"omegad{x[chr(99) + chr(113)]}"]
    y = dict(x)
    y["Om"] = x["Om"] * f
    r1b.append(abs(theta(c_first, y)) / PI2)
    r3b.append(abs(theta(c_third, y)) / PI2)
print(f"   puertas donde el operador X del canal U NO es el cubit de control usado: {nop}; coeficiente omegad de otro cubit: {nmis} de {len(gates)}")
stats("orden 1 con omegad de h_str", r1b)
stats("orden 3 con omegad de h_str", r3b)
