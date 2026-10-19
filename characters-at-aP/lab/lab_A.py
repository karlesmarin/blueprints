# lab_A.py — pegamento del laboratorio del Teorema A (corre en el navegador con Pyodide).  No reimplementa nada:
# usa evlib.py del suplemento (el mismo fichero, copiado sin cambios): Nq, pure (formula del Teorema A) y
# chi_ps + rational_value (caracter EXACTO en Z[zeta_q]).
import json
from math import gcd
import evlib as E


def lab(m, k, lam_txt):
    m, k = int(m), int(k)
    t = 2 * m + 2
    if not (1 <= m <= 8):
        return json.dumps({'error': 'm must be between 1 and 8'})
    if not (1 <= k < t):
        return json.dumps({'error': 'k must be between 1 and %d' % (t - 1)})
    try:
        lam = [int(x) for x in lam_txt.replace(';', ',').split(',') if x.strip()]
    except ValueError:
        return json.dumps({'error': 'lambda must be a list of integers, e.g. 2,1,0'})
    lam = (lam + [0] * m)[:m]
    if any(lam[i] < lam[i + 1] for i in range(m - 1)) or (lam and lam[-1] < 0) or max(lam + [0]) > 30:
        return json.dumps({'error': 'lambda must be a partition (weakly decreasing, >= 0, entries <= 30)'})
    d = gcd(k, t)
    q, p = t // d, k // d
    rho = E.rho(m)
    ell = [lam[i] + rho[i] for i in range(m)]
    nl, nr = E.Nq(ell, q), E.Nq(rho, q)
    # valor exacto en g_{1/q}; en las potencias de a_P todo caracter es entero racional (Prop. de clasificacion),
    # asi que es invariante por Galois y coincide con el valor en g_{p/q}.
    chi = E.rational_value(E.chi_ps(list(lam), 1, q), q)
    formula = int(E.pure(lam, p, q)) if nl == nr else 0
    clases = {}
    for x in ell:
        c = min(x % q, (-x) % q)
        clases.setdefault(c, []).append(x)
    filas = []
    for c in sorted(set(min(r, (q - r) % q) for r in range(q))):
        fija = (2 * c) % q == 0
        cap = d // 2 if fija else d
        filas.append({'clase': c, 'fija': fija, 'cap': cap, 'l': clases.get(c, [])})
    # desglose de la formula: raices positivas e_i-e_j, e_i+e_j (i<j) y 2e_i con su valor en ell y en rho
    raices = []
    for i in range(m):
        for j in range(i + 1, m):
            raices.append(('e%d-e%d' % (i + 1, j + 1), ell[i] - ell[j], rho[i] - rho[j]))
            raices.append(('e%d+e%d' % (i + 1, j + 1), ell[i] + ell[j], rho[i] + rho[j]))
        raices.append(('2e%d' % (i + 1), 2 * ell[i], 2 * rho[i]))
    div_l = [(n, a) for n, a, b in raices if a % q == 0]
    div_r = [(n, b) for n, a, b in raices if b % q == 0]
    Zl = 1
    for _, a in div_l:
        Zl *= a
    Zr = 1
    for _, b in div_r:
        Zr *= b
    Epq = E.Epq(lam, p, q)
    # Teorema B (si chi != 0): factores por clase (evlib.Delta, del suplemento) y kappa por la regla del paper
    factores, kappa, Dval = [], None, None
    if chi:
        Dval, et = E.Delta(list(lam), q)
        n0 = len(et.get(0, ('Sp', []))[1])
        kappa = 1 if (d % 2 == 1 or 2 * n0 < d) else 2
        for c in sorted(et):
            tp, nu = et[c]
            dimf = {'Sp': E.dim_Sp, 'SO': E.dim_SOodd, 'GL': E.dim_GL}[tp](nu)
            factores.append({'clase': c, 'tipo': tp, 'n': len(nu), 'nu': nu, 'dim': int(dimf)})
        Dval = int(Dval)
    return json.dumps({'m': m, 'k': k, 't': t, 'd': d, 'q': q, 'p': p, 'lam': lam, 'ell': ell, 'rho': rho,
                       'Nq_ell': nl, 'Nq_rho': nr, 'chi': chi, 'formula': formula,
                       'acuerdo': chi == formula, 'filas': filas,
                       'div_l': div_l, 'div_r': div_r, 'Zl': Zl, 'Zr': Zr, 'E': Epq,
                       'factores': factores, 'kappa': kappa, 'Delta': Dval,
                       'acuerdoB': (chi == 0) or (abs(chi) == kappa * Dval)})
