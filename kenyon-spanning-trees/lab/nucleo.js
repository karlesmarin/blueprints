// encaje: aritmética del lab JS de kenyon-spanning-trees (Kirchhoff con BigInt/Bareiss, grados, cuota de árboles por
// arista, colocación 3D determinista); lo usan labs.js en la página y control_js.js en node. Mirado: el motor extremal
// certificador de Excovery (Python con nauty: no corre en el navegador; su comprobador sí se usa en lab/comprueba_lab.py
// como referencia independiente) y lab3d.js de Lemmario (solo dibuja).
/* Everything that is checked is exact (BigInt). Floating point is used only to place vertices in the drawings. */
(function (root) {
  'use strict';

  /* Kirchhoff's matrix-tree theorem (K1 of the paper), for a multigraph: L = D − A with multiplicities, τ = any
     cofactor; here the determinant of L without its last row and column, by fraction-free Bareiss elimination
     (every division is exact). edges: [[u, v, k], ...] with k the multiplicity. Returns a BigInt. */
  function tau(n, edges) {
    if (n === 1) return 1n;
    var L = [], i, j, k;
    for (i = 0; i < n; i++) { L.push([]); for (j = 0; j < n; j++) L[i].push(0n); }
    edges.forEach(function (e) {
      var u = e[0], v = e[1], w = BigInt(e[2] === undefined ? 1 : e[2]);
      if (u === v) return;  // a loop lies in no spanning tree
      L[u][u] += w; L[v][v] += w; L[u][v] -= w; L[v][u] -= w;
    });
    var N = n - 1, M = L.slice(0, N).map(function (r) { return r.slice(0, N); }), prev = 1n, sign = 1n;
    for (k = 0; k < N; k++) {
      if (M[k][k] === 0n) {  // pivot: swap with a lower row
        var p = -1;
        for (i = k + 1; i < N; i++) if (M[i][k] !== 0n) { p = i; break; }
        if (p < 0) return 0n;  // singular: disconnected
        var t = M[k]; M[k] = M[p]; M[p] = t; sign = -sign;
      }
      for (i = k + 1; i < N; i++) {
        for (j = k + 1; j < N; j++) M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) / prev;
        M[i][k] = 0n;
      }
      prev = M[k][k];
    }
    return sign * M[N - 1][N - 1];
  }

  /* Degrees counting multiplicities (the paper's convention). */
  function degrees(n, edges) {
    var d = [];
    for (var i = 0; i < n; i++) d.push(0);
    edges.forEach(function (e) { d[e[0]] += e[2]; d[e[1]] += e[2]; });
    return d;
  }

  /* The degree sequence as in the paper's Table 2 (4^2 3^4 = two vertices of degree 4, four of degree 3):
     [[degree, count], ...], largest degree first. */
  function degreeWord(deg) {
    var c = {};
    deg.forEach(function (x) { c[x] = (c[x] || 0) + 1; });
    return Object.keys(c).map(Number).sort(function (a, b) { return b - a; }).map(function (x) { return [x, c[x]]; });
  }

  /* For each edge class uv: the number of spanning trees through ONE given copy, τ(G) − τ(G − copy). Their sum over
     all copies is (n − 1)·τ(G), since every spanning tree has n − 1 edges (an exact check). By (K2) of the paper the
     share (τ(G) − τ(G − f))/τ(G) is the effective resistance R_uv. */
  function treesThrough(n, edges, T) {
    if (T === undefined) T = tau(n, edges);
    return edges.map(function (e, idx) {
      var less = edges.map(function (f, j) { return j === idx ? [f[0], f[1], f[2] - 1] : f; })
                      .filter(function (f) { return f[2] > 0; });
      return T - tau(n, less);
    });
  }

  /* A deterministic 3D placement (no randomness: the same graph is always drawn the same way): vertices start on a
     Fibonacci sphere, then a force-directed relaxation (springs on edges, repulsion between all pairs), centred and
     scaled to radius 1. Only for the drawing. */
  function layout3d(n, edges, iters) {
    var P = [], i, j, it, NIT = iters || 600;
    if (n === 2) return [[-0.8, 0, 0], [0.8, 0, 0]];
    for (i = 0; i < n; i++) {
      var y = 1 - 2 * (i + 0.5) / n, r = Math.sqrt(1 - y * y), ph = i * 2.399963229728653;
      P.push([r * Math.cos(ph), y, r * Math.sin(ph)]);
    }
    var K = 1.1 / Math.cbrt(n), T0 = 0.25;
    for (it = 0; it < NIT; it++) {
      var F = P.map(function () { return [0, 0, 0]; }), temp = T0 * (1 - it / NIT) + 0.002;
      for (i = 0; i < n; i++) for (j = i + 1; j < n; j++) {
        var d = [P[i][0] - P[j][0], P[i][1] - P[j][1], P[i][2] - P[j][2]], l = Math.hypot(d[0], d[1], d[2]) || 1e-6;
        var f = K * K / l;
        for (var c = 0; c < 3; c++) { F[i][c] += d[c] / l * f; F[j][c] -= d[c] / l * f; }
      }
      edges.forEach(function (e) {
        var a = e[0], b = e[1], d = [P[a][0] - P[b][0], P[a][1] - P[b][1], P[a][2] - P[b][2]];
        var l = Math.hypot(d[0], d[1], d[2]) || 1e-6, f = l * l / K;
        for (var c = 0; c < 3; c++) { F[a][c] -= d[c] / l * f; F[b][c] += d[c] / l * f; }
      });
      for (i = 0; i < n; i++) {
        var lf = Math.hypot(F[i][0], F[i][1], F[i][2]) || 1e-9, s = Math.min(lf, temp) / lf;
        for (var c2 = 0; c2 < 3; c2++) P[i][c2] += F[i][c2] * s;
      }
    }
    var cen = [0, 1, 2].map(function (c) { return P.reduce(function (s, p) { return s + p[c]; }, 0) / n; });
    P = P.map(function (p) { return [p[0] - cen[0], p[1] - cen[1], p[2] - cen[2]]; });
    var R = Math.max.apply(null, P.map(function (p) { return Math.hypot(p[0], p[1], p[2]); })) || 1;
    return P.map(function (p) { return [p[0] / R, p[1] / R, p[2] / R]; });
  }

  /* Reduced fraction a/b of BigInts as a string, and its decimal value rounded to some places. */
  function gcd(a, b) { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) { var t = a % b; a = b; b = t; } return a; }
  function frac(a, b) { var g = gcd(a, b) || 1n; a /= g; b /= g; return b === 1n ? String(a) : a + '/' + b; }
  function dec(a, b, places) {
    var pl = places || 4, p = 10n ** BigInt(pl), q = (a * p * 2n + b) / (2n * b), s = String(q).padStart(pl + 1, '0');
    return s.slice(0, -pl) + '.' + s.slice(-pl);
  }

  var api = { tau: tau, degrees: degrees, degreeWord: degreeWord, treesThrough: treesThrough, layout3d: layout3d,
              frac: frac, dec: dec, gcd: gcd };
  root.KenyonNucleo = api;
  if (typeof module !== 'undefined') module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
