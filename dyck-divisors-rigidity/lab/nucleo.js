// encaje: núcleo aritmético EXACTO de los labs JS del blueprint dyck-divisors-rigidity (paper II de Caballero):
// celdas de las rectas Λ + hθ = ρ, vectores c, Z(c), Σ(c), palabras, fibras, secciones A_{a,b}(θ), R(a,b) por
// Alekseyev, fórmulas cerradas de [I] y la Conjetura 9.8. Sin red; lo comprueba labjs/control_js.js contra Python
// (lab/ref_python.json, del enumerador fila_a_c.py del paper). Mirado: el catálogo (cotas BSR, certificado de
// Kantorovich y labweb: otros problemas o solo prueban), dyck-divisors/labjs/nucleo.js (paper I: celdas de a = 1, 2
// y la palabra de n; aquí cualquier a ≤ 4, Σ, fibras y secciones) y kenyon/labjs/nucleo.js (otro problema).
/* Every number that a check depends on is computed with integers (Number when it is provably below 2^53, BigInt for
   R(a,b) and the integers n); floating point is used only to place drawings (cell polygons). */
(function (root) {
  'use strict';

  function gcd(x, y) { x = Math.abs(x); y = Math.abs(y); while (y) { var t = x % y; x = y; y = t; } return x; }
  function lcm(x, y) { return x / gcd(x, y) * y; }
  function fdiv(p, q) { return Math.floor(p / q); }            // q > 0, |p| < 2^53: exact floor of p/q
  function clip(v, b) { return Math.min(b, Math.max(-b - 1, v)); }
  function f(v, b) { return Math.min(b + 1, Math.max(0, v + 1)); }

  // ------------------------------------------------------------------------ counts in closed form (BigInt)
  function bgcd(x, y) { x = x < 0n ? -x : x; y = y < 0n ? -y : y; while (y) { var t = x % y; x = y; y = t; } return x; }
  /* eq. (1): R(a,b) = 1 + a + b + 2ab + V(2b,2a)/2, V(m,n) = Σ_{gcd(i,j)=1} (m+1−i)(n+1−j) (Alekseyev). */
  function Ralek(a, b) {
    var m = 2 * b, n = 2 * a, V = 0n;
    for (var i = 1; i <= m; i++) for (var j = 1; j <= n; j++) if (gcd(i, j) === 1) V += BigInt((m + 1 - i) * (n + 1 - j));
    if (V % 2n) throw new Error('V(2b,2a) odd');
    return BigInt(1 + a + b + 2 * a * b) + V / 2n;
  }
  function phi(q) { var c = 0; for (var p = 1; p <= q; p++) if (gcd(p, q) === 1) c++; return c; }
  /* C_a = Σ_{q≤2a} (2a+1−q) φ(q)/q as [numerator, denominator] (BigInt, reduced). */
  function Ca(a) {
    var N = 0n, D = 1n;
    for (var q = 1; q <= 2 * a; q++) {
      var n = BigInt((2 * a + 1 - q) * phi(q)), d = BigInt(q);
      N = N * d + n * D; D = D * d;
      var g = bgcd(N, D); N /= g; D /= g;
    }
    return [N, D];
  }
  function Phi(q, x) { var c = 0; for (var p = 1; p <= x; p++) if (gcd(p, q) === 1) c++; return c; }
  /* Theorem A of [I] (b ≥ 2), Theorem B of [I] (b ≥ 3), Conjecture 9.8 (b ≥ 5): exact integers or null outside. */
  function WthmA(b) { return b >= 2 ? Math.floor((9 * b * b + 8 * b + 12) / 4) : null; }
  var EB = [30, 33, 8, 27, 36, 5];
  function WthmB(b) { if (b < 3) return null; var t = 44 * b * b + 19 * b + EB[b % 6]; if (t % 6) throw new Error('B'); return t / 6; }
  var H4 = [0, 1, -1, 17];
  function E3conj(b) {
    if (b < 5) return null;
    var q = function (x, y) { return Math.floor(x / y); };
    return 9 * b + 2 * q(b + 1, 3) + q(b - 1, 2) + H4[b % 4];
  }
  /* the lower bound of the proof of Theorem 6.1: Σ_{h≤a} #{j ≤ b: gcd(j,h) = 1} + Σ_{2≤j≤a} ⌊b/j⌋ ([I, Remark 7.6]) */
  function Elower(a, b) {
    var s = 0;
    for (var h = 1; h <= a; h++) s += Phi(h, b);
    for (var j = 2; j <= a; j++) s += Math.floor(b / j);
    return s;
  }

  // ------------------------------------------------------------------------ Z(c), Σ(c), the word
  /* c is the array (c_{−a}, …, c_a); index of c_h is a + h. */
  function H(a, b, c) {
    var rows = [];
    for (var i = 0; i <= a; i++) {
      var r = [];
      for (var j = 0; j <= b; j++) {
        var s = 0;
        for (var l = 0; l <= a; l++) { var h = i - l; s += f(c[a + h] + j, b); }
        r.push(s);
      }
      rows.push(r);
    }
    return rows;
  }
  function Z(a, b, c) {
    var z = [].concat.apply([], H(a, b, c));
    return z.sort(function (x, y) { return x - y; });
  }
  function key(z) { return z.join(','); }
  function Sigma(a, b, c) { return Z(a, b, c).reduce(function (s, v) { return s + v; }, 0); }
  /* the word from Z(c) (Lemma P): the k-th closing bracket is preceded by the k-th smallest element of Z openings. */
  function wordFromZ(z) {
    var w = '', open = 0;
    z.forEach(function (v) { while (open < v) { w += '('; open++; } w += ')'; });
    var K = z.length;
    while (open < K) { w += '('; open++; }
    return w;
  }

  // ------------------------------------------------------------------------ exact enumeration of the cells
  /* Every cell meets, in each vertical strip between consecutive abscissas θ ∈ 𝒯 of the vertices (θ = p/q, q ≤ 2a),
     each vertical line of the strip (proof of Proposition 3.5); on a rational line θ = th2/S, one rational point
     between consecutive crossings Λ = ρ − hθ gives each cell. Units: θ in 1/S, Λ in 1/(2S), S = 2·lcm(1..2a). The
     same sweep as the paper’s fila_a_c.vectores_c. Returns {vecs: [c], wit: [[Λ2, 2S, th2, S]]} (witness Λ = Λ2/(2S),
     θ = th2/S). */
  function cells(a, b) {
    var q = 1;
    for (var d = 1; d <= 2 * a; d++) q = lcm(q, d);
    var cuts = {};
    for (d = 1; d <= 2 * a; d++) for (var num = 0; num <= (2 * b + 2) * d; num++) cuts[num * (q / d)] = 1;
    var cs = Object.keys(cuts).map(Number).sort(function (x, y) { return x - y; });
    var th2s = [];
    for (var i = 0; i + 1 < cs.length; i++) th2s.push(cs[i] + cs[i + 1]);
    th2s.push(2 * cs[cs.length - 1] + 2);
    var S = 2 * q, seen = {}, vecs = [], wit = [];
    th2s.forEach(function (th2) {
      var crit = {};
      for (var h = -a; h <= a; h++) for (var r = -b; r <= b; r++) { var v = r * S - h * th2; if (v > 0) crit[v] = 1; }
      var cr = Object.keys(crit).map(Number).sort(function (x, y) { return x - y; }), pts = [];
      if (!cr.length) pts = [2];
      else {
        pts.push(cr[0]);
        for (var k = 0; k + 1 < cr.length; k++) pts.push(cr[k] + cr[k + 1]);
        pts.push(2 * cr[cr.length - 1] + 2);
      }
      pts.forEach(function (L2) {
        var c = [];
        for (var hh = -a; hh <= a; hh++) c.push(clip(fdiv(L2 + hh * 2 * th2, 2 * S), b));
        var kk = c.join(',');
        if (!seen[kk]) { seen[kk] = 1; vecs.push(c); wit.push([L2, 2 * S, th2, S]); }
      });
    });
    return { vecs: vecs, wit: wit };
  }

  /* Fibres: groups of vectors with one Z. */
  function fibres(a, b, vecs) {
    var byKey = {}, order = [], zs = [];
    vecs.forEach(function (c, i) {
      var z = Z(a, b, c), k = key(z);
      zs.push(z);
      if (!byKey[k]) { byKey[k] = []; order.push(k); }
      byKey[k].push(i);
    });
    var id = new Array(vecs.length);
    order.forEach(function (k, j) { byKey[k].forEach(function (i) { id[i] = j; }); });
    return { keys: order, members: order.map(function (k) { return byKey[k]; }), id: id, zs: zs };
  }

  function leq(c, d) { for (var i = 0; i < c.length; i++) if (c[i] > d[i]) return false; return true; }

  /* Everything Section 3 asserts, checked on one (a, b) exactly. */
  function analyse(a, b) {
    var C = cells(a, b), V = C.vecs, Fb = fibres(a, b, V), R = V.length, W = Fb.keys.length;
    var E = R - W, amb = 0, maxFib = 0, comparable = 0, steps = 0, stepBad = 0, O0 = -1, K = (a + 1) * (b + 1);
    Fb.members.forEach(function (m, j) {
      if (m.length > 1) amb += m.length;
      maxFib = Math.max(maxFib, m.length);
      for (var x = 0; x < m.length; x++) for (var y = x + 1; y < m.length; y++)
        if (leq(V[m[x]], V[m[y]]) || leq(V[m[y]], V[m[x]])) comparable++;
      var z = Fb.zs[m[0]], isO = z.length === K && z.every(function (v, i) { return v === i + 1; });
      if (isO) O0 = j;
    });
    var sig = V.map(function (c) { return Sigma(a, b, c); });
    // Proposition 3.1(a) on every realisable c and every coordinate with c_h ≤ b − 1
    V.forEach(function (c, i) {
      for (var h = -a; h <= a; h++) {
        if (c[a + h] > b - 1) continue;
        var d = c.slice(); d[a + h] += 1;
        var got = Sigma(a, b, d) - sig[i], want = (a + 1 - Math.abs(h)) * (b + 1 - Math.abs(c[a + h] + 1));
        steps++;
        if (got !== want) stepBad++;
      }
    });
    var fibBound = 1;
    for (var qq = 1; qq <= 2 * a; qq++) fibBound += Phi(qq, 2 * b);
    var sizes = {};
    Fb.members.forEach(function (m, j) { if (j !== O0) sizes[m.length] = (sizes[m.length] || 0) + 1; });
    return { a: a, b: b, R: R, W: W, E: E, amb: amb, maxFib: maxFib, comparable: comparable, steps: steps,
             stepBad: stepBad, fibBound: fibBound, O0: O0, sizes: sizes, vecs: V, wit: C.wit, fib: Fb, sig: sig };
  }

  // ------------------------------------------------------------------------ the integer n = 2^(e−1) r^a s^b
  function bpow(x, k) { var r = 1n; x = BigInt(x); for (var i = 0; i < k; i++) r *= x; return r; }
  /* c_h = clip(⌊log(t r^h)/log s⌋), t = 2^e, by exact comparisons s^ρ < t r^h (no equality: 2-adic valuation). */
  function vecOfInteger(a, b, r, s, e) {
    var t = bpow(2, e), c = [];
    for (var h = -a; h <= a; h++) {
      var best = -b - 1;
      for (var rho = -b; rho <= b; rho++) {
        var lhs = t * bpow(r, Math.max(h, 0)) * bpow(s, Math.max(-rho, 0));
        var rhs = bpow(s, Math.max(rho, 0)) * bpow(r, Math.max(-h, 0));
        if (rhs < lhs) best = rho;
      }
      c.push(best);
    }
    return c;
  }
  /* the word read from the definition: D_n △ 2D_n = D_m ∪ t·D_m (m = r^a s^b odd), in increasing order. */
  function wordOfInteger(a, b, r, s, e) {
    var t = bpow(2, e), items = [];
    for (var i = 0; i <= a; i++) for (var j = 0; j <= b; j++) {
      var d = bpow(r, i) * bpow(s, j);
      items.push([d, '(']); items.push([t * d, ')']);
    }
    items.sort(function (x, y) { return x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : 0; });
    return items.map(function (x) { return x[1]; }).join('');
  }
  function isPrime(n) { if (n < 2 || n % 1) return false; for (var d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; }

  // ------------------------------------------------------------------------ Proposition 6.3 and the sections
  /* (i)–(ii): for 0 ≤ k ≤ K − 2, P1(k) = ((k+1/2)/(a+1), 1/(a+1)), P2(k) = (k+1/2, b+1). */
  function twonum(a, b) {
    var K = (a + 1) * (b + 1), out = [];
    for (var k = 0; k <= K - 2; k++) {
      var c1 = [], c2 = [];
      for (var h = -a; h <= a; h++) {
        c1.push(clip(fdiv(2 * (k + h) + 1, 2 * (a + 1)), b));    // Λ + hθ = (2(k+h)+1)/(2(a+1))
        c2.push(clip(k + h * (b + 1), b));                        // Λ + hθ = k + h(b+1) + 1/2
      }
      var z1 = Z(a, b, c1), z2 = Z(a, b, c2), want = [];
      for (var N = 0; N < K; N++) want.push(Math.min(K, N + k + 1));
      want.sort(function (x, y) { return x - y; });
      out.push({ k: k, c1: c1, c2: c2, z1: z1, z2: z2, okZ: key(z1) === key(z2) && key(z1) === key(want),
                 differ: c1.join(',') !== c2.join(',') });
    }
    return out;
  }
  /* A_{a,b}(θ) for θ = P/Q: the proportion of {θ} × (0, b + aθ) in cells of fibre ≥ 2, exactly, as [num, den]
     (lengths in units 1/(2Q)). sizeOf(c) = size of the fibre of c. */
  function section(a, b, P, Q, sizeOf) {
    var top = 2 * (b * Q + a * P), br = {};                 // b + aθ in units 1/(2Q)
    br[0] = 1; br[top] = 1;
    for (var h = -a; h <= a; h++) for (var r = -b; r <= b; r++) { var v = 2 * (r * Q - h * P); if (v > 0 && v < top) br[v] = 1; }
    var xs = Object.keys(br).map(Number).sort(function (x, y) { return x - y; }), amb = 0;
    for (var i = 0; i + 1 < xs.length; i++) {
      var mid = (xs[i] + xs[i + 1]) / 2, c = [];          // xs even: mid is an integer, off every line
      for (var hh = -a; hh <= a; hh++) c.push(clip(fdiv(mid + 2 * hh * P, 2 * Q), b));
      if (sizeOf(c) > 1) amb += xs[i + 1] - xs[i];
    }
    return [amb, top];
  }

  // ------------------------------------------------------------------------ drawing only (floating point)
  /* the polygon of the cell of c inside the window [0, Tmax] × [0, Lmax] of the plane (θ, Λ), by clipping. */
  function polygon(a, b, c, Tmax, Lmax) {
    var poly = [[0, 0], [Tmax, 0], [Tmax, Lmax], [0, Lmax]];
    function cut(A, B, C0) {   // keep A·θ + B·Λ + C0 > 0
      var out = [];
      for (var i = 0; i < poly.length; i++) {
        var p = poly[i], q2 = poly[(i + 1) % poly.length];
        var fp = A * p[0] + B * p[1] + C0, fq = A * q2[0] + B * q2[1] + C0;
        if (fp >= 0) out.push(p);
        if ((fp >= 0) !== (fq >= 0)) { var t = fp / (fp - fq); out.push([p[0] + t * (q2[0] - p[0]), p[1] + t * (q2[1] - p[1])]); }
      }
      poly = out;
    }
    for (var h = -a; h <= a && poly.length; h++) {
      var v = c[a + h];
      if (v >= -b) cut(h, 1, -v);              // Λ + hθ > v
      if (v <= b - 1 && poly.length) cut(-h, -1, v + 1);   // Λ + hθ < v + 1
    }
    return poly.length >= 3 ? poly : null;
  }

  var api = { gcd: gcd, clip: clip, f: f, Ralek: Ralek, Ca: Ca, Phi: Phi, WthmA: WthmA, WthmB: WthmB, E3conj: E3conj,
              Elower: Elower, H: H, Z: Z, key: key, Sigma: Sigma, wordFromZ: wordFromZ, cells: cells, fibres: fibres,
              analyse: analyse, vecOfInteger: vecOfInteger, wordOfInteger: wordOfInteger, isPrime: isPrime,
              twonum: twonum, section: section, polygon: polygon };
  root.RigidNucleo = api;
  if (typeof module !== 'undefined') module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
