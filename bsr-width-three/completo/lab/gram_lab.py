# encaje: laboratorio del blueprint bsr-width-three: el espectraedro de Gram de una forma m×3 y su punto de rango 2m (numpy; Pyodide)
"""The Gram spectrahedron of an m×3 biquadratic sum of squares F (Chua–Plaumann–Sinn–Vinzant, «Gram spectrahedra»): the
positive semidefinite 3m×3m matrices G with v(x,y)ᵀ G v(x,y) = F, v = x ⊗ y. F is a sum of r squares exactly when this
convex set contains a matrix of rank at most r; Theorem 1 says there is always one of rank at most 2m.

The lab takes F = sum of 3m random squares (its Gram matrix G0 has full rank 3m, an interior point), finds a Gram matrix
G* of rank 2m numerically (Levenberg–Marquardt on 2m bilinear forms) and draws the slice of the spectrahedron through G0
and G* (plane: G0 + s(G* − G0) + t·B, B a random direction among the 2×2-minor matrices, which do not change F), coloured
by rank, and the boundary of a 3-dimensional slice. G* sits on the boundary at s = 1, where the rank drops to 2m."""
import numpy as np

import labkit as K


def idx(i, j):
    return 3 * i + j          # coordinate of x_i y_j in V = R^m ⊗ R^3


def minor_basis(m):
    """Orthonormal basis (as vectors of length (3m)²) of the symmetric matrices v ↦ 0: spans of the 2×2 minors."""
    n = 3 * m
    mats = []
    for i in range(m):
        for k in range(i + 1, m):
            for j in range(3):
                for l in range(j + 1, 3):
                    M = np.zeros((n, n))
                    a, b, c, d = idx(i, j), idx(k, l), idx(i, l), idx(k, j)
                    M[a, b] += 1
                    M[b, a] += 1
                    M[c, d] -= 1
                    M[d, c] -= 1
                    mats.append(M.ravel())
    Q, _ = np.linalg.qr(np.array(mats).T)
    return Q


def low_rank_gram(G0, m, r, rng, tries=8, iters=400):
    """W (3m×r) with W Wᵀ ≡ G0 modulo the minors, by Levenberg–Marquardt; returns (W, residual)."""
    n = 3 * m
    Q = minor_basis(m)

    def res(W):
        D = (W @ W.T - G0).ravel()
        return D - Q @ (Q.T @ D)

    best = (None, np.inf)
    for _ in range(tries):
        W = rng.standard_normal((n, r)) * np.sqrt(np.trace(G0) / (n * r))
        mu = 1e-2
        for _ in range(iters):
            F = res(W)
            f = F @ F
            if f < 1e-24:
                break
            J = np.zeros((n * n, n * r))
            for a in range(n):
                for c in range(r):
                    E = np.zeros((n, n))
                    E[a, :] += W[:, c]
                    E[:, a] += W[:, c]
                    v = E.ravel()
                    J[:, a * r + c] = v - Q @ (Q.T @ v)
            A = J.T @ J
            g = J.T @ F
            step = np.linalg.solve(A + mu * np.diag(np.diag(A) + 1e-12), -g)
            W2 = W + step.reshape(n, r)
            F2 = res(W2)
            if F2 @ F2 < f:
                W, mu = W2, max(mu / 3, 1e-12)
            else:
                mu *= 4
        e = np.sqrt(res(W) @ res(W))
        if e < best[1]:
            best = (W, e)
        if e < 1e-9:
            break
    return best


def setup(m, seed):
    rng = np.random.default_rng(seed)
    n = 3 * m
    H = rng.standard_normal((n, n))
    G0 = H @ H.T / n
    W, err = low_rank_gram(G0, m, 2 * m, rng)
    Gs = W @ W.T
    Q = minor_basis(m)
    B = (Q @ rng.standard_normal(Q.shape[1])).reshape(n, n)
    B = (B + B.T) / 2
    B /= np.linalg.norm(B) / np.linalg.norm(Gs - G0)
    C = (Q @ rng.standard_normal(Q.shape[1])).reshape(n, n)
    C = (C + C.T) / 2
    C /= np.linalg.norm(C) / np.linalg.norm(Gs - G0)
    # 8-nov: escala cada dirección de menores a su extensión en el espectraedro (si no, el corte sale aplastado)
    cuerda = lambda M: min(_hasta(G0, M), 3.0) + min(_hasta(G0, -M), 3.0)
    cD = cuerda(Gs - G0)
    for M in (B, C):
        M *= cuerda(M) / cD                # misma cuerda que la dirección de G* (el cuerpo no sale aplastado)
    return G0, Gs, B, C, err


def _hasta(G0, d, hi=50.0):
    """mayor λ con G0 + λd semidefinida positiva (bisección)."""
    lo = 0.0
    if np.linalg.eigvalsh(G0 + hi * d)[0] > 0:
        return hi
    for _ in range(40):
        mid = (lo + hi) / 2
        if np.linalg.eigvalsh(G0 + mid * d)[0] > 0:
            lo = mid
        else:
            hi = mid
    return lo


def rank(G, tol=1e-7):
    w = np.linalg.eigvalsh(G)
    return int((w > tol * max(1.0, w[-1])).sum()), w[0]


COLORS = {'out': '#f4f1ec', 'in': '#cfe3ea', 'edge': '#1B6F8C', 'low': '#B5530F'}


def slice_svg(G0, Gs, B, m, N=90, title=''):
    """Heat map of the plane G0 + s(G*−G0) + tB: outside (not PSD), inside (rank 3m), boundary (rank < 3m)."""
    W, H, L, T = 420, 470, 46, 30
    D = Gs - G0

    def borde(d):          # última t (o s) con G PSD a lo largo de la dirección d desde G0
        lo, hi = 0.0, 8.0
        for _ in range(30):
            mid = (lo + hi) / 2
            if np.linalg.eigvalsh(G0 + mid * d)[0] > 0:
                lo = mid
            else:
                hi = mid
        return lo
    smin, smax = -min(max(borde(-D) * 1.15, 0.35), 1.5), 1.15
    tmax = max(borde(B), borde(-B), borde(D + B), borde(D - B)) * 1.15
    ss = np.linspace(smin, smax, N)
    ts = np.linspace(-tmax, tmax, N)
    lam = np.empty((N, N))
    for a, s in enumerate(ss):
        for b, t in enumerate(ts):
            w = np.linalg.eigvalsh(G0 + s * D + t * B)
            lam[a, b] = w[0] / w[-1]          # relativo: el borde es una línea fina
    PH = H - T - 90                       # alto del dibujo; debajo, eje y leyenda en tres líneas
    cw, ch = (W - L - 10) / N, PH / N
    o = ['<svg viewBox="0 0 %d %d" style="max-width:100%%;background:#fff" xmlns="http://www.w3.org/2000/svg">' % (W, H)]
    o.append('<text x="%d" y="18" font-size="12" text-anchor="middle">%s</text>' % (W / 2, K.esc(title)))
    dentro = lam > 0
    for a in range(N):
        for b in range(N):
            if dentro[a, b]:
                vecinos = [dentro[x, y] for x, y in ((a - 1, b), (a + 1, b), (a, b - 1), (a, b + 1)) if 0 <= x < N and 0 <= y < N]
                col = COLORS['edge'] if not all(vecinos) else COLORS['in']
            else:
                col = COLORS['out']
            o.append('<rect x="%.1f" y="%.1f" width="%.2f" height="%.2f" fill="%s"/>'
                     % (L + a * cw, T + (N - 1 - b) * ch, cw + 0.4, ch + 0.4, col))
    X = lambda s: L + (s - ss[0]) / (ss[-1] - ss[0]) * (W - L - 10)
    Y = lambda t: T + (ts[-1] - t) / (ts[-1] - ts[0]) * PH
    o.append('<circle cx="%.1f" cy="%.1f" r="5" fill="#333"/><text x="%.1f" y="%.1f" font-size="11">G₀ (rank %d)</text>'
             % (X(0), Y(0), X(0) + 7, Y(0) - 6, 3 * m))
    o.append('<path d="M%.1f %.1f l7 -12 l7 12 z" fill="%s" stroke="#333"/><text x="%.1f" y="%.1f" font-size="11" fill="%s" '
             'text-anchor="end">G* (rank %d)</text>' % (X(1) - 7, Y(0) + 6, COLORS['low'], X(1) - 10, Y(0) + 20, COLORS['low'], 2 * m))
    o.append('<text x="%d" y="%d" font-size="11" text-anchor="middle">s: from G₀ (s = 0) towards G* (s = 1)</text>'
             % ((W + L) / 2, T + PH + 18))
    o.append('<text x="14" y="%d" font-size="11" transform="rotate(-90 14 %d)" text-anchor="middle">t: a 2×2-minor '
             'direction</text>' % (T + PH / 2, T + PH / 2))
    legend = [('in', 'inside: positive definite Gram matrices, rank 3m'), ('edge', 'boundary: rank below 3m'),
              ('out', 'outside: not positive semidefinite')]
    for k, (c, txt) in enumerate(legend):
        y = T + PH + 34 + 14 * k
        o.append('<rect x="%d" y="%d" width="10" height="10" fill="%s" stroke="#999"/><text x="%d" y="%d" font-size="10">%s'
                 '</text>' % (L, y, COLORS[c], L + 14, y + 9, K.esc(txt)))
    o.append('</svg>')
    return {'kind': 'svg', 'svg': ''.join(o), 'title': title}


def boundary_3d(G0, Gs, B, C, m, n_dir=520):
    """Points of the boundary of the 3-dimensional slice G0 + s(G*−G0) + tB + uC, by bisection along rays from G0."""
    D = Gs - G0

    def rayos(c, n):
        """puntos del borde por bisección desde el punto interior G0 + c·(D, B, C)."""
        Gc = G0 + c[0] * D + c[1] * B + c[2] * C
        out = []
        k = np.arange(n) + 0.5
        phi = np.arccos(1 - 2 * k / n)
        th = np.pi * (1 + 5 ** 0.5) * k
        for p, q in zip(phi, th):
            d = np.array([np.sin(p) * np.cos(q), np.sin(p) * np.sin(q), np.cos(p)])
            M = d[0] * D + d[1] * B + d[2] * C
            lo, hi = 0.0, 6.0
            if np.linalg.eigvalsh(Gc + hi * M)[0] > 0:
                continue                   # sin borde en esta dirección dentro del encuadre
            for _ in range(28):
                mid = (lo + hi) / 2
                if np.linalg.eigvalsh(Gc + mid * M)[0] > 0:
                    lo = mid
                else:
                    hi = mid
            out.append(c + lo * d)
        return out

    # 8-nov: G0 está cerca de una cara y los rayos desde G0 se amontonan; se lanzan desde el centroide de una 1.ª pasada
    c = np.mean(rayos(np.zeros(3), 120), axis=0)
    return [list(p) for p in rayos(c, n_dir)]


def run_gram(params):
    import json
    p = json.loads(params) if isinstance(params, str) else params
    m, seed = int(p.get('m', 3)), int(p.get('seed', 1))
    if not 2 <= m <= 4:
        return K.error('m must be between 2 and 4')
    G0, Gs, B, C, err = setup(m, seed)
    r0, _ = rank(G0)
    rs, lmin = rank(Gs)
    if err > 1e-6:
        return K.error('the search for a Gram matrix of rank 2m did not converge (residual %.1e); try another seed' % err)
    _, err1 = low_rank_gram(G0, m, 2 * m - 1, np.random.default_rng(seed + 1), tries=4, iters=300)
    menos = ('A Gram matrix of rank 2m − 1 was also found (residual %.1e): this random F needs fewer squares; the '
             'theorem bounds every F, and Lemma 6 gives one that needs exactly 2m.' % err1 if err1 < 1e-8 else
             'No Gram matrix of rank 2m − 1 was found in this search (residual %.1e); a search is not a proof.' % err1)
    pts = boundary_3d(G0, Gs, B, C, m)
    vista = K.three_d([K.points3(pts, name='boundary of the slice (rank < 3m)', color='#1B6F8C', size=2.5, opacity=0.5),
                       K.points3([[0, 0, 0]], name='G₀, rank %d (interior)' % r0, color='#333333', size=8),
                       K.points3([[1, 0, 0]], name='G*, rank %d (Theorem 1)' % rs, color='#B5530F', size=11, star=True)],
                      title='a 3-dimensional slice of the Gram spectrahedron of F', axes=('s', 't', 'u'))
    plano = slice_svg(G0, Gs, B, m, title='the plane through G₀ and G*, coloured by rank')
    txt = ('m = %d. F is a sum of 3m = %d random squares; its Gram matrices form a convex set of 3m×3m positive '
           'semidefinite matrices of dimension %d (the 2×2-minor directions). A Gram matrix of rank %d = 2m was found '
           '(residual %.1e): F is a sum of 2m squares, as Theorem 1 says. %s'
           % (m, 3 * m, 3 * (m * (m - 1) // 2), rs, err, menos))
    return K.result(txt, [plano, vista], K.table(['matrix', 'rank', 'where'],
                                                 [['G₀ (the 3m random squares)', r0, 'interior'],
                                                  ['G* (found)', rs, 'on the boundary']]))


def random_gram():
    import json
    import random
    return json.dumps({'m': str(random.choice([2, 3, 3, 4])), 'seed': str(random.randint(1, 999))})
