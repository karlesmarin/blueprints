# Version 3 of qsl-diagnostics, lower bound: EXACT (SymPy) eigenvalues of K†K, K = P_SS (H¹ + H²) P_AA on two copies,
# giving ||K||² = 23/2 J² and T_* ≥ π/(√46 J). Transmon basis (b = [[0,1,0],[0,0,√2],[0,0,0]]); ∧² and Sym² do not
# depend on the basis. H_c/J = b⊗b† + b†⊗b.
import itertools
import sympy as sp

b = sp.Matrix([[0, 1, 0], [0, 0, sp.sqrt(2)], [0, 0, 0]])
h = sp.kronecker_product(b, b.H) + sp.kronecker_product(b.H, b)        # sobre A⊗B, índice a*3 + b


def idx(a1, a2, b1, b2):
    return ((a1 * 3 + a2) * 3 + b1) * 3 + b2


# H¹ + H² en A1 A2 B1 B2 (81), como matriz dispersa por diccionario
H = {}
for a1, a2, b1, b2, x1, x2, y1, y2 in itertools.product(range(3), repeat=8):
    v = 0
    if a2 == x2 and b2 == y2:
        v += h[a1 * 3 + b1, x1 * 3 + y1]
    if a1 == x1 and b1 == y1:
        v += h[a2 * 3 + b2, x2 * 3 + y2]
    if v != 0:
        H[(idx(a1, a2, b1, b2), idx(x1, x2, y1, y2))] = v
# bases ortonormales de AA (∧²⊗∧², 9) y SS (Sym²⊗Sym², 36)
def asim():
    return [{(i, j): 1 / sp.sqrt(2), (j, i): -1 / sp.sqrt(2)} for i, j in itertools.combinations(range(3), 2)]


def sim():
    out = [{(i, i): 1} for i in range(3)]
    out += [{(i, j): 1 / sp.sqrt(2), (j, i): 1 / sp.sqrt(2)} for i, j in itertools.combinations(range(3), 2)]
    return out


def prod(u, v):
    return {idx(a1, a2, b1, b2): cu * cv for (a1, a2), cu in u.items() for (b1, b2), cv in v.items()}


AA = [prod(u, v) for u in asim() for v in asim()]
SS = [prod(u, v) for u in sim() for v in sim()]


def aplicar(vec):
    out = {}
    for (r, c), hv in H.items():
        if c in vec:
            out[r] = out.get(r, 0) + hv * vec[c]
    return out


Hcols = [aplicar(v) for v in AA]
K = sp.Matrix(len(SS), len(AA), lambda i, j: sp.nsimplify(sp.expand(sum(c * Hcols[j].get(k, 0) for k, c in SS[i].items()))))
M = sp.simplify(K.H * K)
ev = M.eigenvals()
print('eigenvalues of K†K (with multiplicities):', ev)
mx = max(ev, key=lambda e: float(e))
print('||K||² =', mx, ' == 23/2 :', sp.simplify(mx - sp.Rational(23, 2)) == 0)
print('bound T* ≥ pi/(2||K||) =', sp.nsimplify(sp.pi / (2 * sp.sqrt(mx))), '=', sp.N(sp.pi / (2 * sp.sqrt(mx)), 15))
