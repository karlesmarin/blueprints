# encaje: laboratorio del blueprint de inversion-height-two (Figura 4, Teoremas 5.1, 5.2, 7.2, 7.3); corre en el
# navegador con Pyodide (Lemmario).
"""Lab of Figure 4: the Smith profiles as a water level.

Each matrix of a panel (the target and the allowed denominators, evaluated on the exact arc) is a column of bars, one
per Smith part over Q[[t]]; at level j the water hides the parts < j and ν_j counts the bars that stick out. At the
level of the proof the target keeps more bars out than the bound on allowed denominators allows: the margin.

The parts are the paper's own data (lab/smith_profiles.json, copied from figuras/datos_smith.json: computed in
F_p[[t]]/t^N with two primes that agree). The lab recounts ν_j from the parts and checks it against the profiles the
paper plotted, and checks the margin, before drawing."""
import json

PANELS = {  # level of the proof, bound on allowed denominators there, top level drawn, title (fig_4_perfiles_smith.py)
    'a': (2, 'Theorem 5.1: \\(\\mathcal U_1\\), arc \\(\\gamma_{%(k)s}\\), level \\(j=k+1\\)'),
    'b': (2, 'Theorem 5.2, r = 3: \\(\\mathcal U_2\\), arc \\(\\gamma_{%(k)s}\\), level \\(j=(r-1)k+1\\)'),
    'c': (4, "Theorem 7.2: \\(\\Gamma'_2\\), arc \\(\\gamma_{%(k)s}\\), level \\(j=k+1\\)"),
    'd': (8, "Theorem 7.3, k = 6: \\(\\Gamma'_4\\), arc \\(\\gamma_{%(k)s}\\), level \\(j=\\kappa+1\\)"),
}
LETTERS = 'ABCDEFGH'


def tex(name):
    """The paper's names are $…$ TeX: the page's MathJax reads \\( … \\)."""
    parts = name.split('$')
    return ''.join(p if i % 2 == 0 else '\\(' + p + '\\)' for i, p in enumerate(parts))


def nu(parts, j):
    return sum(1 for p in parts if p is None or p >= j)


def run(params):
    p = json.loads(params)
    key = str(p.get('panel', 'a')).strip().lower().strip('()')
    if key not in PANELS:
        return json.dumps({'error': 'panel must be a, b, c or d (the four panels of Figure 4)'})
    every = json.load(open('smith_profiles.json', encoding='utf8'))['panels']
    figs, texts = {}, {}
    for k in sorted(PANELS):
        r = panel(k, every[k])
        if 'error' in r:
            return json.dumps(r)
        figs[k], texts[k] = r['fig'], r['text']
    whole = {'kind': 'levels', 'title': 'Figure 4 as a water level', 'panels': [figs[k] for k in sorted(figs)],
             'start_panel': sorted(figs).index(key), 'figure': 'fig_4_perfiles_smith', 'panel': 'a'}
    return json.dumps({'text': texts[key] + ' The four panels are checked; Figure 4 shows them in its place (tabs).',
                       'plots': [whole]})


def panel(key, data):
    """One panel of Figure 4: the figure and its text, after the checks (or {'error': …})."""
    bound, title = PANELS[key]
    jstar = data['j']
    cols = []
    for role in ('target', 'allowed', 'contrast'):
        for name, parts in data[role].items():
            cols.append({'name': tex(name), 'short': LETTERS[len(cols)], 'parts': parts, 'role': role})
    # checks before drawing: the profile recounted from the parts is the one the paper plotted, and the margin holds
    bad = [c['short'] for c in cols if [nu(c['parts'], j) for j in range(1, len(data['nu'][_raw(data, c)]) + 1)]
           != data['nu'][_raw(data, c)]]
    if bad:
        return {'error': 'panel %s: ν recounted from the parts differs from the paper for %s: report this' % (key, bad)}
    tg = max(nu(c['parts'], jstar) for c in cols if c['role'] == 'target')
    al = max(nu(c['parts'], jstar) for c in cols if c['role'] == 'allowed')
    top = max(max((x for x in c['parts'] if x is not None), default=0) for c in cols)
    fig = {'kind': 'levels', 'tab': '(%s) Theorem %s' % (key, {'a': '5.1', 'b': '5.2', 'c': '7.2', 'd': '7.3'}[key]),
           'title': 'Figure 4(%s) as a water level' % key, 'columns': cols, 'mark': jstar,
           'bound': bound, 'max': max(top, jstar) + 2, 'label': 'Smith part (exponent of t)', 'start': 1}
    k = data['k']
    text = ('%s. Each bar is a Smith part of the matrix on the exact arc; raise the water to the level j and count what '
            'sticks out: that is ν<sub>j</sub>, the curve of the paper\'s Figure 4(%s). At level %d the target has %d parts '
            'out, every allowed denominator at most %d (bound) — here at most %d. Checked before drawing: ν<sub>j</sub> '
            'recounted from the parts equals the paper\'s profile for every matrix and level. Data: the paper\'s '
            'computation (two primes).' % (title % {'k': k}, key, jstar, tg, bound, al))
    if not tg > bound >= al:
        text += ' ⚠️ The margin does not hold in these data: report this.'
    return {'fig': fig, 'text': text}


def _raw(data, col):
    """The paper's name of a column (the key of its profile)."""
    for role in ('target', 'allowed', 'contrast'):
        for name in data[role]:
            if tex(name) == col['name'] and role == col['role']:
                return name
    raise KeyError(col['name'])
