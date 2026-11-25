// encaje: núcleo de los labs JS del blueprint dyck-divisors (aritmética exacta con BigInt; sin red). Traduce las
// funciones de lab/dyck_divisors_lab.py; labjs/control_js_python.js lo coteja con ese fichero (con control negativo).
// Mirado el catálogo (prueba de lector de labs en Chrome, Enclosure, rango SOS): ninguna hace esta aritmética en JS.
/* Exact arithmetic of the labs of «How Many Dyck Words Do the Divisors of an Integer Make?».
   Every quantity the labs check (word, counts C(n), cell vector, Z(c), R(a,b), W(a,b)) is computed with integers
   (BigInt where they can be large) or exact rationals; floating point is used only to place points in the drawings.
   All internal calls go through the object N, so that a test can corrupt one function and see the effect. */
(function (root) {
  'use strict';
  var N = {};

  function bcmp(a, b) { return a < b ? -1 : (a > b ? 1 : 0); }
  function bgcd(a, b) { if (a < 0n) a = -a; if (b < 0n) b = -b; while (b) { var t = a % b; a = b; b = t; } return a; }
  function gcd(a, b) { while (b) { var t = a % b; a = b; b = t; } return a; }
  function bpow(x, e) { var r = 1n; for (var i = 0; i < e; i++) r *= x; return r; }
  N.bcmp = bcmp; N.bgcd = bgcd; N.gcd = gcd; N.bpow = bpow;

  // ------------------------------------------------------------------------------------------ arithmetic of n
  /* Prime factorisation by trial division (n <= 10^12): [[p, e], ...] with p increasing (BigInt p, Number e). */
  N.factor = function (n) {
    n = BigInt(n);
    var out = [], p = 2n;
    while (p * p <= n) {
      var e = 0;
      while (n % p === 0n) { n /= p; e++; }
      if (e) out.push([p, e]);
      p += (p === 2n) ? 1n : 2n;
    }
    if (n > 1n) out.push([n, 1]);
    return out;
  };

  N.divisors = function (n) {
    var ds = [1n], fac = N.factor(n);
    for (var i = 0; i < fac.length; i++) {
      var p = fac[i][0], e = fac[i][1], nd = [];
      for (var j = 0; j < ds.length; j++) { var x = ds[j]; for (var k = 0; k <= e; k++) { nd.push(x); x *= p; } }
      ds = nd;
    }
    return ds.sort(bcmp);
  };

  /* <<n>>_2 from the definition: D_n symmetric difference 2D_n in increasing order, '(' for D_n \ 2D_n, ')' for
     2D_n \ D_n. */
  N.wordDefinition = function (n) {
    var D = N.divisors(n), inD = new Set(), in2 = new Set(), all = [];
    D.forEach(function (d) { inD.add(d.toString()); });
    D.forEach(function (d) { in2.add((2n * d).toString()); });
    D.forEach(function (d) { if (!in2.has(d.toString())) all.push([d, '(']); });
    D.forEach(function (d) { var x = 2n * d; if (!inD.has(x.toString())) all.push([x, ')']); });
    all.sort(function (u, v) { return bcmp(u[0], v[0]); });
    return all.map(function (u) { return u[1]; }).join('');
  };

  /* The multiset C(n) of (1): for each divisor d' of the odd part m, #{d | m : d < t d'}, sorted (t = 2^e).
     Returns {m, t, e1, cs}. The count is by binary search in the sorted divisors (same set, exact comparisons). */
  N.countsC = function (n) {
    var m = BigInt(n), e1 = 0;
    while (m % 2n === 0n) { m /= 2n; e1++; }
    var t = bpow(2n, e1 + 1), Dm = N.divisors(m), cs = [];
    for (var j = 0; j < Dm.length; j++) {
      var bound = t * Dm[j], lo = 0, hi = Dm.length;  // first index with Dm[i] >= bound
      while (lo < hi) { var mid = (lo + hi) >> 1; if (Dm[mid] < bound) lo = mid + 1; else hi = mid; }
      cs.push(lo);
    }
    cs.sort(function (a, b) { return a - b; });
    return { m: m, t: t, e1: e1, cs: cs };
  };

  N.wordFromCounts = function (cs) {
    var out = '', prev = 0;
    for (var i = 0; i < cs.length; i++) { out += '('.repeat(cs[i] - prev) + ')'; prev = cs[i]; }
    return out;
  };

  N.heights = function (w) {
    var h = 0, out = [0];
    for (var i = 0; i < w.length; i++) { h += (w[i] === '(') ? 1 : -1; out.push(h); }
    return out;
  };

  N.clip = function (v, b) { return Math.min(b, Math.max(-b - 1, v)); };
  N.f = function (v, b) { return Math.min(b + 1, Math.max(0, v + 1)); };

  /* Z(c) of Section 6, Step 1, sorted; c is indexed h = -a .. a (c[h + a]). */
  N.Z = function (a, b, c) {
    var out = [];
    for (var ip = 0; ip <= a; ip++)
      for (var jp = 0; jp <= b; jp++) {
        var s = 0;
        for (var i = 0; i <= a; i++) s += N.f(c[(ip - i) + a] + jp, b);
        out.push(s);
      }
    return out.sort(function (x, y) { return x - y; });
  };

  /* s^rho < t r^h, moving negative powers to the other side (BigInt). */
  N.below = function (r, s, t, rho, h) {
    var lhs = bpow(s, Math.max(rho, 0)) * bpow(r, Math.max(-h, 0));
    var rhs = t * bpow(r, Math.max(h, 0)) * bpow(s, Math.max(-rho, 0));
    return lhs < rhs;
  };

  /* c_h = clip floor(Lambda + h theta), Lambda = log t / log s, theta = log r / log s, EXACTLY:
     floor(Lambda + h theta) >= rho iff s^rho < t r^h. r, s, t BigInt; a, b Number. */
  N.vectorTwoPrimes = function (r, a, s, b, t) {
    var c = [];
    for (var h = -a; h <= a; h++) {
      var v = -b - 1;
      for (var rho = -b; rho <= b; rho++) if (N.below(r, s, t, rho, h)) v = rho;
      c.push(v);
    }
    return c;
  };

  /* For m = p^(q-1): N = min(floor(log t / log p), q - 1), exactly. */
  N.onePrimeN = function (p, f1, t) {
    var n = 0, x = BigInt(p);
    while (x < t && n < f1) { n++; x *= BigInt(p); }
    return n;
  };

  /* Everything the word lab checks, for one n (BigInt or string). */
  N.wordData = function (n) {
    n = BigInt(n);
    var w = N.wordDefinition(n), C = N.countsC(n), fac = N.factor(C.m), hs = N.heights(w);
    var k = w.length / 2, rev = w.split('').reverse().map(function (ch) { return ch === '(' ? ')' : '('; }).join('');
    var out = { n: n.toString(), word: w, m: C.m.toString(), t: C.t.toString(), e1: C.e1, cs: C.cs, k: k,
                ok_C: N.wordFromCounts(C.cs) === w, dyck: Math.min.apply(null, hs) === 0 && hs[hs.length - 1] === 0,
                sym: w === rev, height: Math.max.apply(null, hs),
                factor: fac.map(function (x) { return [x[0].toString(), x[1]]; }) };
    if (fac.length === 1) {
      var q = fac[0][0], e = fac[0][1], Nn = N.onePrimeN(q, e, C.t), oc = [];
      for (var j = 1; j <= e + 1; j++) oc.push(Math.min(e + 1, Nn + j));
      out.oneprime = { N: Nn, q: e + 1, same: N.wordFromCounts(oc) === w };
    } else if (fac.length === 2) {
      var fs = fac.slice().sort(function (u, v) { return (u[1] - v[1]) || bcmp(u[0], v[0]); });
      var r = fs[0][0], a = fs[0][1], s = fs[1][0], b = fs[1][1];
      var c = N.vectorTwoPrimes(r, a, s, b, C.t);
      out.twoprimes = { r: r.toString(), a: a, s: s.toString(), b: b, c: c,
                        same: N.Z(a, b, c).join(',') === C.cs.join(',') };
    }
    if (k >= 2) {
      var fin = [];
      N.factor(BigInt(k)).forEach(function (x) { for (var i = 0; i < x[1]; i++) fin.push(Number(x[0]) - 1); });
      out.finest = fin.sort(function (x, y) { return y - x; });
    }
    return out;
  };

  // ------------------------------------------------------------------------------------- exact rationals (BigInt)
  function Q(n, d) {
    n = BigInt(n); d = (d === undefined) ? 1n : BigInt(d);
    if (d < 0n) { n = -n; d = -d; }
    var g = bgcd(n, d); if (g > 1n) { n /= g; d /= g; }
    return { n: n, d: d };
  }
  N.Q = Q;
  N.qadd = function (x, y) { return Q(x.n * y.d + y.n * x.d, x.d * y.d); };
  N.qsub = function (x, y) { return Q(x.n * y.d - y.n * x.d, x.d * y.d); };
  N.qmulInt = function (x, k) { return Q(x.n * BigInt(k), x.d); };
  N.qhalf = function (x) { return Q(x.n, x.d * 2n); };
  N.qcmp = function (x, y) { return bcmp(x.n * y.d, y.n * x.d); };
  N.qfloor = function (x) { var q = x.n / x.d; if (x.n % x.d !== 0n && x.n < 0n) q -= 1n; return Number(q); };
  N.qkey = function (x) { return x.n + '/' + x.d; };
  N.qstr = function (x) { return x.d === 1n ? x.n.toString() : x.n + '/' + x.d; };

  function uniqSorted(list) {
    var seen = {}, out = [];
    list.forEach(function (x) { var k = N.qkey(x); if (!seen[k]) { seen[k] = 1; out.push(x); } });
    return out.sort(N.qcmp);
  }
  function samples(xs) {  // a point below the first, one between consecutive ones, one beyond the last
    var out = [N.qhalf(xs[0])];
    for (var i = 0; i + 1 < xs.length; i++) out.push(N.qhalf(N.qadd(xs[i], xs[i + 1])));
    out.push(N.qadd(xs[xs.length - 1], Q(1)));
    return out;
  }

  // ------------------------------------------------------------------------------------------ cells and words
  N.phi = function (q) { var s = 0; for (var k = 1; k <= q; k++) if (gcd(k, q) === 1) s++; return s; };
  N.Phi = function (q, x) { var s = 0; for (var p = 1; p <= x; p++) if (gcd(p, q) === 1) s++; return s; };

  /* Theorem 5.1: R(a,b) = 1 + (3a+1)b + a + 1/2 sum_{q=1}^{2a} [(2a+1-q) S_q(b) - B_q(a,b)],
     B_q = 2 sum_{k=1}^{floor(a/q)} Phi_q(floor(b/k)). */
  N.Rformula = function (a, b) {
    var s = 0;
    for (var q = 1; q <= 2 * a; q++) {
      var S = 0, B = 0;
      for (var p = 1; p <= 2 * b; p++) if (gcd(p, q) === 1) S += 2 * b - p + 1;
      for (var k = 1; k <= Math.floor(a / q); k++) B += N.Phi(q, Math.floor(b / k));
      s += (2 * a + 1 - q) * S - 2 * B;
    }
    if (s % 2 !== 0) throw new Error('R formula: odd sum');
    return 1 + (3 * a + 1) * b + a + s / 2;
  };

  /* C_a = sum_{q <= 2a} (2a+1-q) phi(q)/q, exact. */
  N.Ca = function (a) {
    var x = Q(0);
    for (var q = 1; q <= 2 * a; q++) x = N.qadd(x, Q((2 * a + 1 - q) * N.phi(q), q));
    return x;
  };

  /* The realisable clipped vectors c, by exact rational sample points: between consecutive critical slopes theta
     (and beyond them) one point between consecutive crossings Lambda = rho - h theta > 0 meets every cell.
     Returns an array of vectors (each an array of Numbers), one per cell. */
  N.cells = function (a, b) {
    var crit = [];
    for (var q = 1; q <= 2 * a; q++) for (var p = 1; p <= 2 * b; p++) crit.push(Q(p, q));
    var ths = samples(uniqSorted(crit)), seen = {}, out = [];
    ths.forEach(function (th) {
      var xs = [];
      for (var h = -a; h <= a; h++) for (var rho = -b; rho <= b; rho++) xs.push(N.qsub(Q(rho), N.qmulInt(th, h)));
      xs = uniqSorted(xs).filter(function (x) { return x.n > 0n; });
      var Ls = xs.length ? samples(xs) : [Q(1)];
      Ls.forEach(function (L) {
        var c = [];
        for (var h = -a; h <= a; h++) c.push(N.clip(N.qfloor(N.qadd(L, N.qmulInt(th, h))), b));
        var key = c.join(',');
        if (!seen[key]) { seen[key] = 1; out.push(c); }
      });
    });
    return out;
  };

  N.WA = function (b) { return Math.floor((9 * b * b + 8 * b + 12) / 4); };
  N.EB = [30, 33, 8, 27, 36, 5];
  N.WB = function (b) {
    var v = 44 * b * b + 19 * b + N.EB[b % 6];
    if (v % 6 !== 0) throw new Error('W_B not an integer');
    return v / 6;
  };
  N.R2 = function (b) { return Math.floor((22 * b * b + 31 * b + 9 + (b % 3 === 1 ? 1 : 0)) / 3); };
  N.LIMIT = { 1: 30, 2: 18, 3: 12, 4: 9, 5: 7, 6: 5 };

  /* One row of the cells lab: R by the formula and by recount, W (distinct Z(c)), closed form, check. */
  N.cellRow = function (a, b) {
    var vecs = N.cells(a, b), Rc = vecs.length, Rf = N.Rformula(a, b), words = new Set();
    vecs.forEach(function (c) { words.add(N.Z(a, b, c).join(',')); });
    var Wc = words.size, closed = null;
    if (a === 1 && b >= 2) closed = N.WA(b);
    if (a === 2 && b >= 3) closed = N.WB(b);
    var ok = Rc === Rf && (closed === null || closed === Wc) && (a !== 2 || N.R2(b) === Rc);
    return { b: b, Rf: Rf, Rc: Rc, Wc: Wc, closed: closed, R2: a === 2 ? N.R2(b) : null, ok: ok };
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = N;
  else root.DyckNucleo = N;
})(typeof window !== 'undefined' ? window : this);
