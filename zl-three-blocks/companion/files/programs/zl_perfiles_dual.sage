# Theorem E: exact rational duals of the profile LPs (Sage, PPL backend).
import json
import sys
from pathlib import Path

for f in sys.argv[1:]:
    d = json.load(open(f))
    nv = d['nv']
    p = MixedIntegerLinearProgram(maximization=False, solver='PPL')
    u = p.new_variable(real=True, nonnegative=False)
    v = p.new_variable(nonnegative=True)
    w = p.new_variable(nonnegative=True)
    col = {k: [] for k in range(nv)}
    for i, (r, h) in enumerate(d['eq']):
        for a, b in r.items():
            col[int(a)].append(b * u[i])
    for i, (r, h) in enumerate(d['ge']):
        for a, b in r.items():
            col[int(a)].append(-b * v[i])
    for i, (r, h) in enumerate(d['le']):
        for a, b in r.items():
            col[int(a)].append(b * w[i])
    c = {int(a): b for a, b in d['c'].items()}
    for k in range(nv):
        expr = p.sum(col[k]) if col[k] else 0
        if col[k]:
            p.add_constraint(expr >= c.get(k, 0))
        elif c.get(k, 0) > 0:
            raise ValueError('columna sin restricciones con coste positivo: primal no acotado')
    obj = p.sum(h * u[i] for i, (r, h) in enumerate(d['eq'])) + p.sum(h * w[i] for i, (r, h) in enumerate(d['le'])) \
        - p.sum(h * v[i] for i, (r, h) in enumerate(d['ge']))
    p.set_objective(obj)
    try:
        val = QQ(p.solve())
    except Exception as e:
        print(f, 'DUAL NO FACTIBLE O ERROR (primal no acotado o infactible):', type(e).__name__, e)
        continue
    U = [QQ(p.get_values(u[i])) for i in range(len(d['eq']))]
    V = [QQ(p.get_values(v[i])) for i in range(len(d['ge']))]
    W = [QQ(p.get_values(w[i])) for i in range(len(d['le']))]
    res = {'perfil': d['perfil'], 'valor': [int(val.numerator()), int(val.denominator())],
           'u': [[int(x.numerator()), int(x.denominator())] for x in U],
           'v': [[int(x.numerator()), int(x.denominator())] for x in V],
           'w': [[int(x.numerator()), int(x.denominator())] for x in W]}
    out = Path(f).with_name('cert_' + Path(f).name)
    json.dump(res, open(str(out), 'w'))
    print(Path(f).name, 'perfil', d['perfil'], 'cota =', val)
