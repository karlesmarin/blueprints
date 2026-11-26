// encaje: interfaz de los cuatro labs JS del blueprint dyck-divisors-rigidity (formulario, ejemplos, 🎲, 3D primero
// con su 2D al lado, SVG, tabla con los colores del paper, CSV, enlace); la aritmética exacta está en nucleo.js y los
// datos en datos.js (generado por lab/hacer_datos.py). Lo instala excovery.lemmario.labjs (engine = 'js'); sin red.
// Mirado: el catálogo (labweb solo prueba), kenyon-spanning-trees/labjs/labs.js (mismo cableado, copiado y adaptado).
/* Four labs, each a <div data-dk-lab="..."> written by labjs/lab_<name>.html, with result panels marked data-lm-out.
   Each computes its default input as soon as the script runs (no click needed). The 3D figure always comes first. */
(function () {
  'use strict';
  var N = window.RigidNucleo, D = window.RigidDatos;
  // the paper's colours (Okabe-Ito): one per a (figuras/comun.py), and the row categories of its tables
  var COLOR_A = { 1: '#000000', 2: '#0072B2', 3: '#D55E00', 4: '#009E73', 5: '#CC79A7' };
  var ACCENT = '#0072B2', VERM = '#D55E00', PURPLE = '#CC79A7', GREEN = '#009E73', SKY = '#56B4E9', GREY = '#B8C2CC';
  function tint(hex, p) {   // xcolor's hex!p: the colour mixed with white
    var c = [1, 3, 5].map(function (i) { return parseInt(hex.slice(i, i + 2), 16); });
    return '#' + c.map(function (x) { return ('0' + Math.round(255 + (x - 255) * p).toString(16)).slice(-2); }).join('');
  }
  var CAT = { X: tint(VERM, .10), C: tint(ACCENT, .06), Cb: tint(ACCENT, .12), E: tint(GREEN, .07), Eb: tint(GREEN, .14),
              Q: tint(PURPLE, .12), Qb: tint(PURPLE, .24), head: tint(ACCENT, .14), sky: tint(SKY, .25), verm: tint(VERM, .14) };

  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }
  function sw(c) { return '<span style="display:inline-block;width:1.1em;height:.8em;border:1px solid #888;vertical-align:middle;background:' + c + '"></span>'; }
  function intIn(v, lo, hi) { var x = String(v).trim(); return /^-?\d+$/.test(x) && +x >= lo && +x <= hi ? +x : null; }
  function frac(n, d) {   // BigInt or Number -> reduced «n/d» text
    n = BigInt(n); d = BigInt(d);
    var g = n < 0n ? -n : n, h = d; while (h) { var t = g % h; g = h; h = t; }
    if (g === 0n) g = 1n;
    n /= g; d /= g;
    if (d < 0n) { n = -n; d = -d; }
    return d === 1n ? String(n) : n + '/' + d;
  }
  function Cval(a) { var c = D.C[a]; return c[0] / c[1]; }
  var VIR = ['#440154', '#3b528b', '#21918c', '#5ec962', '#fde725'];
  function ramp(t) {      // viridis-like, t in [0, 1]
    t = Math.max(0, Math.min(1, t)) * (VIR.length - 1);
    var i = Math.min(VIR.length - 2, Math.floor(t)), u = t - i;
    var p = function (h, k) { return parseInt(h.slice(k, k + 2), 16); };
    return '#' + [1, 3, 5].map(function (k) { return ('0' + Math.round(p(VIR[i], k) + u * (p(VIR[i + 1], k) - p(VIR[i], k))).toString(16)).slice(-2); }).join('');
  }
  function svgOpen(W, H, label) { return '<svg class="dk-svg" viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="' + esc(label) + '">'; }
  function fig(cap, body) { return '<figure class="dk-fig"><figcaption>' + cap + '</figcaption>' + body + '</figure>'; }

  /* a plain 2D plot: series [{pts: [[x, y]], color, width, dash, dots, name}], axes with ticks */
  function plot(o) {
    var W = o.W || 520, H = o.H || 320, L = 54, R = 14, T = 30, B = 46;
    var X = function (x) { return L + (x - o.x0) / (o.x1 - o.x0) * (W - L - R); };
    var Y = function (y) { return T + (o.y1 - y) / (o.y1 - o.y0) * (H - T - B); };
    var out = [svgOpen(W, H + (o.legend ? 18 * Math.ceil(o.series.length / 2) : 0), o.title)];
    out.push('<text x="' + W / 2 + '" y="16" text-anchor="middle" font-size="13" font-weight="700">' + esc(o.title) + '</text>');
    (o.yt || []).forEach(function (v) {
      out.push('<line x1="' + L + '" x2="' + (W - R) + '" y1="' + Y(v).toFixed(1) + '" y2="' + Y(v).toFixed(1) + '" stroke="#e3e7eb"/>');
      out.push('<text x="' + (L - 6) + '" y="' + (Y(v) + 4).toFixed(1) + '" text-anchor="end" font-size="11">' + v + '</text>');
    });
    (o.xt || []).forEach(function (v) {
      out.push('<text x="' + X(v).toFixed(1) + '" y="' + (H - B + 16) + '" text-anchor="middle" font-size="11">' + v + '</text>');
    });
    out.push('<text x="' + ((L + W) / 2) + '" y="' + (H - B + 32) + '" text-anchor="middle" font-size="12" font-style="italic">' + esc(o.xl) + '</text>');
    out.push('<text x="14" y="' + ((T + H - B) / 2) + '" font-size="12" font-style="italic" transform="rotate(-90 14 ' + ((T + H - B) / 2) + ')" text-anchor="middle">' + esc(o.yl) + '</text>');
    o.series.forEach(function (s) {
      var pts = s.pts.filter(function (p) { return p[1] >= o.y0 - 1e-9 && p[1] <= o.y1 + 1e-9 && p[0] >= o.x0 && p[0] <= o.x1; });
      if (!s.dots) {
        var d = pts.map(function (p, i) { return (i ? 'L' : 'M') + X(p[0]).toFixed(1) + ',' + Y(p[1]).toFixed(1); }).join(' ');
        out.push('<path d="' + d + '" fill="none" stroke="' + s.color + '" stroke-width="' + (s.width || 1.6) + '"' + (s.dash ? ' stroke-dasharray="6 4"' : '') + '/>');
      } else pts.forEach(function (p) {
        out.push('<circle cx="' + X(p[0]).toFixed(1) + '" cy="' + Y(p[1]).toFixed(1) + '" r="' + (s.r || 2.4) + '" fill="' + s.color + '"/>');
      });
    });
    if (o.legend) o.series.forEach(function (s, i) {
      if (!s.name) return;
      var x = L + (i % 2) * (W - L) / 2, y = H + 6 + 18 * Math.floor(i / 2);
      out.push('<line x1="' + x + '" x2="' + (x + 18) + '" y1="' + y + '" y2="' + y + '" stroke="' + s.color + '" stroke-width="' + (s.width || 1.6) + '"' + (s.dash ? ' stroke-dasharray="6 4"' : '') + '/>');
      out.push('<text x="' + (x + 24) + '" y="' + (y + 4) + '" font-size="12">' + esc(s.name) + '</text>');
    });
    out.push('</svg>');
    return out.join('');
  }

  // =========================================================================================== 1. rigidity
  var BMAXA = { 1: 60, 2: 150, 3: 300, 4: 90, 5: 80 };
  function rigidRows(a) {
    return D.rows[a].map(function (r) {
      var b = r[0], R = r[1], W = r[2], E = R - W;
      var Ra = N.Ralek(a, b), closed = a === 1 ? N.WthmA(b) : a === 2 ? N.WthmB(b) : a === 3 ? (N.E3conj(b) === null ? null : R - N.E3conj(b)) : null;
      return { b: b, R: R, W: W, E: E, okR: Ra === BigInt(R), closed: closed, okW: closed === null || closed === W, low: N.Elower(a, b) };
    });
  }
  function runRigid(v) {
    var a = intIn(v.a, 1, 5);
    if (a === null) return { error: 'a must be an integer from 1 to 5 (the exponents the paper enumerated).' };
    var all = {}, bad = false;
    for (var x = 1; x <= 5; x++) all[x] = rigidRows(x);
    var rows = all[a];
    rows.forEach(function (r) { bad = bad || !r.okR || !r.okW || r.E < r.low; });
    // the 3D cascade: for each a a curtain over the runs of consecutive b, isolated values as dots
    var items = [], ZS = 16, XS = 300;
    for (x = 1; x <= 5; x++) {
      var y = (x - 1) / 4, run = [], runs = [], iso = [];
      all[x].forEach(function (r, i) {
        if (r.b < 8) return;
        var prev = all[x][i - 1];
        if (run.length && prev && prev.b === r.b - 1) run.push(r); else { if (run.length) runs.push(run); run = [r]; }
      });
      if (run.length) runs.push(run);
      runs.forEach(function (rn, k) {
        if (rn.length < 2) { iso.push(rn[0]); return; }
        var top = rn.map(function (r) { return [r.b / XS * 1.6, y, r.E / r.b / ZS]; });
        var bot = rn.map(function (r) { return [r.b / XS * 1.6, y, 0]; });
        var it = { type: 'surface', grid: [bot, top], color: COLOR_A[x], opacity: x === a ? 0.55 : 0.25 };
        if (k === 0) it.name = 'a = ' + x + (x === 1 ? ' (positive control: grows like b/4)' : '');
        items.push(it);
        items.push({ type: 'curve', points: top, color: COLOR_A[x], width: x === a ? 2.6 : 1.4 });
      });
      if (iso.length) items.push({ type: 'points', points: iso.map(function (r) { return [r.b / XS * 1.6, y, r.E / r.b / ZS]; }), color: COLOR_A[x], size: 4 });
    }
    items.push({ type: 'curve', points: [[8 / XS * 1.6, 0.25, 43 / 6 / ZS], [1.6, 0.25, 43 / 6 / ZS]], color: '#555', dash: true, name: 'slope 43/6 (a = 2, [I])' });
    items.push({ type: 'curve', points: [[8 / XS * 1.6, 0.5, 61 / 6 / ZS], [1.6, 0.5, 61 / 6 / ZS]], color: '#999', dash: true, name: 'slope 61/6 (a = 3, conjectural)' });
    items.push({ type: 'points', points: rows.filter(function (r) { return r.b >= 8 && r.b % 10 === 0; }).map(function (r) { return [r.b / XS * 1.6, (a - 1) / 4, r.E / r.b / ZS]; }),
                 color: COLOR_A[a], marker: 'star', size: 8, name: 'your a = ' + a + ' (every tenth b)' });
    var spec = { title: 'E(a,b)/b over (b, a), exact enumeration · drag to turn', axes: ['b (8 … 300)', 'a (1 … 5)', 'E/b (0 … 16)'], items: items,
                 flat: function () { return flatRigid(all, a); } };
    var b2 = rows.filter(function (r) { return r.b >= 2 * a; });
    var last = rows[rows.length - 1];
    var nClosed = rows.filter(function (r) { return r.closed !== null; }).length;
    var text = 'a = ' + a + ': ' + rows.length + ' exactly enumerated values of b (b = ' + rows[0].b + ' … ' + last.b + ', from the paper’s logs). ' +
      'R(a,b) recomputed by Alekseyev’s formula in your browser: ' + (rows.every(function (r) { return r.okR; }) ? 'equal in all ✓' : 'MISMATCH ✗') + '. ' +
      (nClosed ? 'W against ' + (a === 1 ? 'Theorem A of [I]' : a === 2 ? 'Theorem B of [I] (b ≥ 3)' : 'the conjectural formula of Conjecture 9.8 (b ≥ 5)') + ': ' +
        (rows.every(function (r) { return r.okW; }) ? 'equal in all ' + nClosed + ' ✓' : 'MISMATCH ✗') + '. ' : 'No closed form of W is known for this a (the theorem gives only its leading term). ') +
      'Lower bound of the proof of Theorem 6.1, E ≥ Σ#{j ≤ b: gcd(j,h) = 1} + Σ⌊b/j⌋: ' + (rows.every(function (r) { return r.E >= r.low; }) ? 'holds in all ✓' : 'FAILS ✗') + '. ' +
      'For b ≥ 2a, E/b lies between ' + Math.min.apply(null, b2.map(function (r) { return r.E / r.b; })).toFixed(3) + ' and ' +
      Math.max.apply(null, b2.map(function (r) { return r.E / r.b; })).toFixed(3) + '; at b = ' + last.b + ', E = ' + last.E + ', E/b = ' + (last.E / last.b).toFixed(3) +
      ', W/(C_a b²) = ' + (last.W / (Cval(a) * last.b * last.b)).toFixed(4) + ' with C_' + a + ' = ' + D.C[a][0] + '/' + D.C[a][1] + '. ' +
      (a === 1 ? 'For a = 1 the excess is quadratic (the exchange of progressions of [I]): the certificate finds it, a positive control.' :
        'Theorem 6.1 (computer-assisted) proves E(a,b) = Θ(b) for this a; the data do not prove anything, they show it.');
    var table = '<div class="dk-tablewrap"><table class="dk-table"><tr style="background:' + CAT.head + '"><th>b</th><th>R(a,b)</th><th>W(a,b)</th><th>E</th><th>E/b</th><th>W/(C_a b²)</th><th>R = Alekseyev</th><th>closed form</th></tr>';
    rows.forEach(function (r, i) {
      var bg = a === 1 ? CAT.X : (i % 2 ? CAT.Cb : CAT.C);
      table += '<tr style="color:#222;background:' + bg + '"><td>' + r.b + '</td><td>' + r.R + '</td><td>' + r.W + '</td><td>' + r.E + '</td><td>' + (r.E / r.b).toFixed(3) +
        '</td><td>' + (r.W / (Cval(a) * r.b * r.b)).toFixed(4) + '</td><td>' + (r.okR ? '✓' : '✗') + '</td><td>' + (r.closed === null ? '–' : r.okW ? '✓ ' + r.closed : '✗ ' + r.closed) + '</td></tr>';
    });
    table += '</table></div><p style="font-size:.9em">Row colours as in the paper’s Table 2: ' + sw(CAT.X) + ' a = 1, the positive control; ' + sw(CAT.C) + sw(CAT.Cb) +
      ' a = 2, …, 5, the certified cases (computer-assisted; the two shades alternate).</p>';
    return { text: text, fig3d: [spec], plots: [], bad: bad, table: table,
             csv: { name: 'rigidity-a' + a + '.csv', head: ['a', 'b', 'R', 'W', 'E'], rows: rows.map(function (r) { return [a, r.b, r.R, r.W, r.E]; }) } };
  }
  function flatRigid(all, a) {
    var series = [];
    for (var x = 1; x <= 5; x++) {
      series.push({ pts: all[x].filter(function (r) { return r.b >= 4; }).map(function (r) { return [r.b, r.W / (Cval(x) * r.b * r.b)]; }),
                    color: COLOR_A[x], width: x === a ? 2.8 : 1.2, dots: x >= 3 && x !== a, r: 1.6, name: 'a = ' + x });
    }
    series.push({ pts: [[0, 1], [300, 1]], color: '#555', dash: true, name: 'limit 1 (a ≥ 2)' });
    series.push({ pts: [[0, 0.9], [300, 0.9]], color: '#000', dash: true, name: 'limit 9/10 (a = 1)' });
    return fig('2D view: W(a,b)/(C_a b²) against b', plot({ title: 'W(a,b)/(C_a b²), exact', x0: 0, x1: 300, y0: 0.55, y1: 1.05,
      xt: [0, 50, 100, 150, 200, 250, 300], yt: [0.6, 0.7, 0.8, 0.9, 1.0], xl: 'b', yl: 'W/(C_a b²)', series: series, legend: true }));
  }
  function randomRigid() { return { a: String(1 + Math.floor(Math.random() * 5)) }; }

  // =========================================================================================== 2. cells
  var BMAXC = { 1: 8, 2: 8, 3: 8, 4: 6 };
  var ODDP = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31];
  function runCells(v) {
    var a = intIn(v.a, 1, 4);
    if (a === null) return { error: 'a must be an integer from 1 to 4.' };
    var b = intIn(v.b, 1, BMAXC[a]);
    if (b === null) return { error: 'for a = ' + a + ', b must be an integer from 1 to ' + BMAXC[a] + ' (so that every cell can be drawn in your browser).' };
    var hasN = String(v.r || '').trim() !== '' || String(v.s || '').trim() !== '' || String(v.e || '').trim() !== '';
    var r = null, s = null, e = null;
    if (hasN) {
      r = intIn(v.r, 3, 1000); s = intIn(v.s, 3, 1000); e = intIn(v.e, 1, 40);
      if (r === null || s === null || e === null || !N.isPrime(r) || !N.isPrime(s) || r === s)
        return { error: 'your integer needs two distinct odd primes r, s ≤ 1000 and 1 ≤ e ≤ 40 (or leave the three boxes empty).' };
    }
    var A = N.analyse(a, b), K = (a + 1) * (b + 1), bad = false;
    var Ra = N.Ralek(a, b), okR = Ra === BigInt(A.R);
    var known = (D.rows[a] || []).filter(function (x) { return x[0] === b; })[0];
    var okW = !known || known[2] === A.W, Wc = a === 1 ? N.WthmA(b) : a === 2 ? N.WthmB(b) : null, okWc = Wc === null || Wc === A.W;
    bad = !okR || !okW || !okWc || A.stepBad > 0 || A.comparable > 0 || A.maxFib > A.fibBound || !(A.E <= A.amb && A.amb <= 2 * A.E);
    var Tmax = 2.2 * b, Lmax = (a + 1) * b;
    var size = function (i) { return A.fib.members[A.fib.id[i]].length; };
    var col = function (i) { return A.fib.id[i] === A.O0 && size(i) > 1 ? SKY : size(i) > 1 ? VERM : GREY; };
    var polys = A.vecs.map(function (c) { return N.polygon(a, b, c, Tmax, Lmax); });
    var inWin = polys.filter(function (p) { return p; }).length;
    var smin = Math.min.apply(null, A.sig), smax = Math.max.apply(null, A.sig);
    var Zs = function (sg) { return (sg - smin) / Math.max(1, smax - smin) * 0.8; };
    var Xs = function (t) { return t / Tmax * 1.4; }, Ys = function (L) { return L / Lmax; };
    var cen = polys.map(function (p) {
      if (!p) return null;
      var x = 0, y = 0; p.forEach(function (q) { x += q[0]; y += q[1]; });
      return [x / p.length, y / p.length];
    });
    var items = [], named = {};
    polys.forEach(function (p, i) {
      if (!p) return;
      var z = Zs(A.sig[i]), c0 = [Xs(cen[i][0]), Ys(cen[i][1]), z];
      var ring = p.concat([p[0]]).map(function (q) { return [Xs(q[0]), Ys(q[1]), z]; });
      var kind = col(i) === SKY ? 'the fibre of O(0)' : col(i) === VERM ? 'a cell whose word is shared' : 'a cell with its own word';
      var it = { type: 'surface', grid: [ring.map(function () { return c0; }), ring], color: col(i), opacity: col(i) === GREY ? 0.35 : 0.75 };
      if (!named[kind]) { it.name = kind; named[kind] = 1; }
      items.push(it);
    });
    // bridges: the cells of one non-trivial fibre joined at their common height Σ
    A.fib.members.forEach(function (m) {
      if (m.length < 2) return;
      var vis = m.filter(function (i) { return polys[i]; });
      for (var k = 0; k + 1 < vis.length; k++) {
        var i = vis[k], j = vis[k + 1], z = Zs(A.sig[i]);
        var it = { type: 'curve', points: [[Xs(cen[i][0]), Ys(cen[i][1]), z], [Xs(cen[j][0]), Ys(cen[j][1]), z]], color: col(i) === SKY ? '#1f6f9c' : '#8a2f00', width: 2.2 };
        if (!named.bridge) { it.name = 'bridge: same word, same height Σ'; named.bridge = 1; }
        items.push(it);
      }
    });
    var nInfo = '', nCell = -1, nPt = null;
    if (hasN) {
      var cn = N.vecOfInteger(a, b, r, s, e), kn = cn.join(',');
      A.vecs.forEach(function (c, i) { if (c.join(',') === kn) nCell = i; });
      var wDef = N.wordOfInteger(a, b, r, s, e), wCell = nCell >= 0 ? N.wordFromZ(A.fib.zs[nCell]) : '';
      var okN = nCell >= 0 && wDef === wCell;
      bad = bad || !okN;
      var th = Math.log(r) / Math.log(s), La = e * Math.log(2) / Math.log(s);
      nPt = [th, La];
      nInfo = ' Your integer n = 2^' + (e - 1) + '·' + r + '^' + a + '·' + s + '^' + b + ' (t = 2^' + e + '): θ = log r/log s ≈ ' + th.toFixed(4) + ', Λ = log t/log s ≈ ' + La.toFixed(4) +
        '; its vector, by exact comparisons s^ρ < t·r^h, is c = (' + cn.join(', ') + ')' + (nCell >= 0 ? ', a cell of the list' : ', NOT among the enumerated cells ✗') +
        '. Its word read from the divisors (D_n △ 2D_n in increasing order) is ' + wDef + (okN ? ' = the word of its cell ✓' : ' ≠ the word of the cell ✗') +
        (nCell >= 0 ? '; the fibre of its word has ' + size(nCell) + ' cell' + (size(nCell) > 1 ? 's' : '') + '.' : '.');
      if (nCell >= 0 && th < Tmax && La < Lmax) items.push({ type: 'points', points: [[Xs(th), Ys(La), Zs(A.sig[nCell]) + 0.02]], color: '#000000', marker: 'star', size: 11, name: 'your integer n' });
    }
    var spec = { title: 'Cells as terraces at height Σ(c), a = ' + a + ', b = ' + b + ' · drag to turn', axes: ['θ (0 … ' + Tmax.toFixed(1) + ')', 'Λ (0 … ' + Lmax + ')', 'Σ(c)'],
                 items: items, flat: function () { return flatCells(a, b, A, polys, col, Tmax, Lmax, nPt, nCell); } };
    var big = Object.keys(A.sizes).filter(function (k) { return +k >= 3; }).map(function (k) { return A.sizes[k] + ' of size ' + k; });
    var text = 'a = ' + a + ', b = ' + b + ': every cell enumerated exactly in your browser. R = ' + A.R + (okR ? ' = Alekseyev’s formula ✓' : ' ≠ Alekseyev (' + Ra + ') ✗') +
      '; W = ' + A.W + ' distinct words' + (known ? (okW ? ' = the paper’s enumeration ✓' : ' ≠ the paper’s data (' + known[2] + ') ✗') : '') +
      (Wc !== null ? (okWc ? ' = Theorem ' + (a === 1 ? 'A' : 'B') + ' of [I] ✓' : ' ≠ Theorem ' + (a === 1 ? 'A' : 'B') + ' (' + Wc + ') ✗') : '') +
      '; E = R − W = ' + A.E + '. Proposition 3.1(a), Σ(c + e_h) − Σ(c) = (a+1−|h|)(b+1−|c_h+1|): ' + A.steps + ' steps, ' + (A.stepBad ? A.stepBad + ' FAIL ✗' : 'all exact ✓') +
      '. Corollary 3.2(ii), no two comparable vectors in a fibre: ' + (A.comparable ? A.comparable + ' comparable pairs ✗' : 'none ✓') +
      '. Proposition 3.5: the largest fibre has ' + A.maxFib + ' cells ≤ 1 + Σ_{q≤2a} Φ_q(2b) = ' + A.fibBound + ' ≤ 4ab + 1 = ' + (4 * a * b + 1) + (A.maxFib <= A.fibBound ? ' ✓' : ' ✗') +
      '. Lemma 3.6: E = ' + A.E + ' ≤ Amb = ' + A.amb + ' ≤ 2E = ' + 2 * A.E + (A.E <= A.amb && A.amb <= 2 * A.E ? ' ✓' : ' ✗') +
      '. The fibre of O(0) (the word ()()…() of semilength K = ' + K + ') has ' + (A.O0 >= 0 ? A.fib.members[A.O0].length : 0) + ' cells' +
      (big.length ? '; outside it, fibres ' + big.join(', ') : '; outside it every fibre has at most two cells') + '. ' +
      inWin + ' of the ' + A.R + ' cells meet the drawn window 0 < θ < ' + Tmax.toFixed(1) + ', 0 < Λ < ' + Lmax + ' (cells are unbounded; the others lie beyond it).' + nInfo;
    var rows = [];
    A.fib.members.forEach(function (m, j) { if (m.length > 1) rows.push(j); });
    rows.sort(function (x, y) { return A.fib.members[y].length - A.fib.members[x].length || x - y; });
    var shown = rows.slice(0, 60);
    var table = '<div class="dk-tablewrap"><table class="dk-table"><tr style="background:' + CAT.head + '"><th>fibre</th><th>cells</th><th>Σ</th><th>vectors c = (c₋ₐ, …, cₐ)</th><th>word</th></tr>';
    shown.forEach(function (j, t) {
      var m = A.fib.members[j], isO = j === A.O0;
      table += '<tr style="color:#222;background:' + (isO ? CAT.sky : CAT.verm) + '"><td>' + (isO ? 'O(0)' : t) + '</td><td>' + m.length + '</td><td>' + A.sig[m[0]] + '</td><td style="text-align:left">' +
        m.map(function (i) { return '(' + A.vecs[i].join(',') + ')'; }).join(' ') + '</td><td style="text-align:left;font-family:monospace">' + esc(N.wordFromZ(A.fib.zs[m[0]])) + '</td></tr>';
    });
    table += '</table></div><p style="font-size:.9em">' + sw(CAT.sky) + ' the fibre of O(0) · ' + sw(CAT.verm) + ' the other fibres of two or more cells' +
      (rows.length > shown.length ? ' (the first ' + shown.length + ' of ' + rows.length + ')' : ' (all ' + rows.length + ')') + '. Every cell of one fibre has the same Σ (it is a function of the word).</p>';
    return { text: text, fig3d: [spec], plots: [], bad: bad, table: table,
             csv: { name: 'cells-a' + a + '-b' + b + '.csv', head: ['vector', 'Sigma', 'fibre', 'fibre_size', 'word'],
                    rows: A.vecs.map(function (c, i) { return ['(' + c.join(' ') + ')', A.sig[i], A.fib.id[i], size(i), N.wordFromZ(A.fib.zs[i])]; }) } };
  }
  function flatCells(a, b, A, polys, col, Tmax, Lmax, nPt, nCell) {
    var W = 520, H = 360, L = 44, R = 12, T = 26, B = 40;
    var X = function (t) { return L + t / Tmax * (W - L - R); }, Y = function (l) { return T + (1 - l / Lmax) * (H - T - B); };
    var out = [svgOpen(W, H + 24, 'cells seen from above')];
    out.push('<text x="' + W / 2 + '" y="16" text-anchor="middle" font-size="13" font-weight="700">the same cells seen from above (θ across, Λ up)</text>');
    polys.forEach(function (p, i) {
      if (!p) return;
      out.push('<polygon points="' + p.map(function (q) { return X(q[0]).toFixed(1) + ',' + Y(q[1]).toFixed(1); }).join(' ') + '" fill="' + col(i) + '" fill-opacity="' + (col(i) === GREY ? 0.35 : 0.8) + '" stroke="#fff" stroke-width="0.6"/>');
    });
    for (var k = 0; k <= Math.floor(Tmax); k += Math.max(1, Math.round(Tmax / 8)))
      out.push('<text x="' + X(k).toFixed(1) + '" y="' + (H - B + 16) + '" text-anchor="middle" font-size="11">' + k + '</text>');
    for (k = 0; k <= Lmax; k += Math.max(1, Math.round(Lmax / 6)))
      out.push('<text x="' + (L - 6) + '" y="' + (Y(k) + 4).toFixed(1) + '" text-anchor="end" font-size="11">' + k + '</text>');
    out.push('<text x="' + ((L + W) / 2) + '" y="' + (H - B + 32) + '" text-anchor="middle" font-size="12" font-style="italic">θ = log r / log s</text>');
    if (nPt && nPt[0] < Tmax && nPt[1] < Lmax) out.push('<text x="' + X(nPt[0]).toFixed(1) + '" y="' + (Y(nPt[1]) + 5).toFixed(1) + '" text-anchor="middle" font-size="16">★</text>');
    var y = H + 10;
    out.push('<rect x="' + L + '" y="' + (y - 9) + '" width="12" height="10" fill="' + SKY + '"/><text x="' + (L + 16) + '" y="' + y + '" font-size="11">fibre of O(0)</text>');
    out.push('<rect x="' + (L + 120) + '" y="' + (y - 9) + '" width="12" height="10" fill="' + VERM + '"/><text x="' + (L + 136) + '" y="' + y + '" font-size="11">shared word</text>');
    out.push('<rect x="' + (L + 240) + '" y="' + (y - 9) + '" width="12" height="10" fill="' + GREY + '"/><text x="' + (L + 256) + '" y="' + y + '" font-size="11">own word</text>');
    out.push('</svg>');
    return fig('2D view: the window from above' + (nPt ? ' (★ your integer)' : ''), out.join(''));
  }
  function randomCells() {
    var a = 1 + Math.floor(Math.random() * 4), b = 1 + Math.floor(Math.random() * BMAXC[a]);
    var r = ODDP[Math.floor(Math.random() * ODDP.length)], s;
    do { s = ODDP[Math.floor(Math.random() * ODDP.length)]; } while (s === r);
    return { a: String(a), b: String(b), r: String(r), s: String(s), e: String(1 + Math.floor(Math.random() * 12)) };
  }

  // =========================================================================================== 3. the tent
  var BMAXT = { 2: 8, 3: 6, 4: 5 };
  function runTent(v) {
    var a = intIn(v.a, 2, 4);
    if (a === null) return { error: 'a must be 2, 3 or 4 (Proposition 6.3 needs a ≥ 2).' };
    var b = intIn(v.b, 2, BMAXT[a]);
    if (b === null) return { error: 'for a = ' + a + ', b must be an integer from 2 to ' + BMAXT[a] + ' (every cell is enumerated in your browser).' };
    var T = D.tent, bad = false, K = (a + 1) * (b + 1), q = K - 1;
    // the paper's surface (a = 2): every 4th θ, b on a log scale
    var step = 4, cols = [];
    for (var j = 0; j < T.ks.length; j += step) cols.push(j);
    if (cols[cols.length - 1] !== T.ks.length - 1) cols.push(T.ks.length - 1);
    var Xt = function (th) { return (th - 0.15) / 0.7 * 1.4; }, Yb = function (bb) { return (Math.log2(bb) - 3) / 4; }, Za = function (z) { return z * 0.8; };
    var grid = T.bs.map(function (bb, i) { return cols.map(function (jj) { return [Xt(T.ks[jj] / T.den), Yb(bb), Za(T.Z[i][jj])]; }); });
    var colors = T.bs.map(function (bb, i) { return cols.map(function (jj) { return ramp(T.Z[i][jj]); }); });
    var i0 = T.ks.indexOf(T.den / 3);
    var fixed = [{ type: 'surface', grid: grid, colors: colors, opacity: 0.85, name: 'A₂,b(θ): ambiguous share of the line {θ} × (0, b+2θ)' },
                 { type: 'curve', points: T.bs.map(function (bb, i) { return [Xt(1 / 3), Yb(bb), Za(T.Z[i][i0]) + 0.004]; }), color: PURPLE, width: 3.2, name: 'the ridge θ = 1/3, height 1 − 1/q' }];
    var tentR = [], tentL = [];
    for (var t = 0; t <= 20; t++) { var d = t / 20 / 6; tentR.push([Xt(1 / 3 + d), Yb(160), Za(1 - 6 * d)]); }
    for (t = 0; t <= 10; t++) { d = t / 10 / 12; tentL.push([Xt(1 / 3 - d), Yb(160), Za(1 - 6 * d)]); }
    fixed.push({ type: 'curve', points: tentR, color: '#333', dash: true, width: 1.8, name: 'limiting lower bound F₂ on the right (Proposition 6.3(iii))' });
    fixed.push({ type: 'curve', points: tentL, color: '#999', dash: true, width: 1.8, name: 'left side, |d| ≤ 1/12: computed, not proved' });
    var frames = T.bs.map(function (bb, i) {
      return [{ type: 'curve', points: T.Z[i].map(function (z, jj) { return [Xt(T.ks[jj] / T.den), Yb(bb), Za(z) + 0.006]; }), color: '#000', width: 2.2, name: 'section at the slider’s b' }];
    });
    var spec = { title: 'The ambiguity profile A₂,b(θ), b = 8 … 128 (exact sections of the paper) · drag to turn', axes: ['θ (0.15 … 0.85)', 'log₂ b (3 … 7)', 'A'],
                 items: fixed, colorbar: { label: 'A₂,b(θ)', stops: [['0', ramp(0)], ['0.5', ramp(0.5)], ['1', ramp(1)]] },
                 slider: { label: 'b', values: T.bs, start: T.bs.indexOf(32), items: frames },
                 flat: function (f) { return flatTent(f); } };
    // the paper's own checks on its data: ridge = 1 − 1/q, and ≥ F_2 − 1/q on the right
    var ridgeOk = T.bs.every(function (bb, i) { return Math.abs(T.Z[i][i0] - (1 - 1 / (3 * bb + 2))) < 2e-6; });
    var boundOk = T.bs.every(function (bb, i) {
      return T.ks.every(function (k, jj) { var dd = k / T.den - 1 / 3; return dd < 0 || dd > 1 / 6 || T.Z[i][jj] >= 1 - 6 * dd - 1 / (3 * bb + 2) - 2e-6; });
    });
    bad = bad || !ridgeOk || !boundOk;
    // live: Proposition 6.3 (i)-(ii) and the exact section for your (a, b)
    var A = N.analyse(a, b), sz = {};
    A.vecs.forEach(function (c, i) { sz[c.join(',')] = A.fib.members[A.fib.id[i]].length; });
    var sizeOf = function (c) { return sz[c.join(',')] || 0; };
    var tn = N.twonum(a, b), okI = tn.every(function (x) { return x.okZ; }), okII = tn.every(function (x) { return x.k > K - 3 || x.differ; });
    var Q = 20 * a * (a + 1), live = [], liveBad = 0;
    for (var jj = -20; jj <= 30; jj++) {
      var P = 20 * a + jj, sec = N.section(a, b, P, Q, sizeOf), dd2 = jj / Q, val = sec[0] / sec[1];
      // Proposition 6.3(iii) on the right (0 ≤ d < 1/(a(a+1))) and (iv) on the left (|d| < 1/(2a(a+1))), u = a(a+1)|d|
      var uu = a * (a + 1) * Math.abs(dd2);
      var bound = dd2 >= 0 && uu < 1 ? (q - 1) * (1 - uu) / (q + uu) : dd2 < 0 && uu < 0.5 ? (q - 1) * (1 - 2 * uu) / (q - uu) : null;
      if (bound !== null && val < bound - 1e-12) liveBad++;
      live.push({ th: P / Q, d: dd2, v: val, num: sec[0], den: sec[1], bound: bound });
    }
    var ridge = live.filter(function (x) { return x.d === 0; })[0], okRidge = ridge.num * q === ridge.den * (q - 1);
    bad = bad || !okI || !okII || liveBad > 0 || !okRidge;
    var text = 'Proposition 6.3 for a = ' + a + ', b = ' + b + ' (K = ' + K + ', q = K − 1 = ' + q + '), recomputed exactly in your browser: (i) for all ' + tn.length +
      ' values 0 ≤ k ≤ K−2, Z(P₁(k)) = Z(P₂(k)) = {min(K, N+k+1)} ' + (okI ? '✓' : '✗') + '; (ii) for k ≤ K−3 the two vectors differ ' + (okII ? '✓' : '✗') +
      ' (at k = K−2 they ' + (tn[tn.length - 1].differ ? 'differ too' : 'coincide') + '). From all ' + A.R + ' cells and their fibres, the exact section A_{a,b}(θ) at ' + live.length +
      ' rational θ near 1/(a+1): at θ = 1/(a+1) it is ' + ridge.num + '/' + ridge.den + (okRidge ? ' = 1 − 1/q ✓' : ' ≠ 1 − 1/q ✗') +
      '; it is ≥ the bounds of Proposition 6.3, (q−1)(1−u)/(q+u) on the right (iii) and (q−1)(1−2u)/(q−u) on the left (iv), u = a(a+1)|d|, at every point ' + (liveBad ? '✗ (' + liveBad + ' failures)' : '✓') + '. ' +
      'In the paper’s data (a = 2, b = 8 … 128, θ = k/720): the ridge equals 1 − 1/q at every b ' + (ridgeOk ? '✓' : '✗') + ' and the right side is above the bound ' + (boundOk ? '✓' : '✗') +
      '. The ridge rises with b while the proportion of ambiguous cells falls like 1/b: cells and lengths are different measures (Corollaries 6.2 and 6.4).';
    var liveSvg = fig('Your (a, b): the exact section near θ = 1/(a+1) against the bound of Proposition 6.3(iii)', plot({
      title: 'A_{' + a + ',' + b + '}(θ), exact', x0: live[0].th, x1: live[live.length - 1].th, y0: 0, y1: 1.02,
      xt: [live[0].th, 1 / (a + 1), 1 / a].map(function (x) { return +x.toFixed(3); }), yt: [0, 0.25, 0.5, 0.75, 1], xl: 'θ', yl: 'A',
      series: [{ pts: live.map(function (x) { return [x.th, x.v]; }), color: COLOR_A[a], width: 2.2, name: 'exact section (' + live.length + ' points)' },
               { pts: live.filter(function (x) { return x.bound !== null; }).map(function (x) { return [x.th, x.bound]; }), color: '#333', dash: true, name: 'bounds (iii) right, (iv) left (proved)' },
               { pts: [[1 / (a + 1), 0], [1 / (a + 1), 1]], color: PURPLE, width: 1, name: 'θ = 1/(a+1)' }], legend: true }));
    var Ilen = T.I[1] - T.I[0];
    var table = '<div class="dk-tablewrap"><table class="dk-table"><tr style="background:' + CAT.head + '"><th>a</th><th>b</th><th>mean P_{a,b}(I), I = [0.14, 6.9]</th><th>bound (a), one side: 1/(2a(a+1)|I|)</th><th>bound (b) at this b, both sides (limit 3/(4a(a+1)|I|))</th><th>Amb/R (cells)</th></tr>';
    T.means.forEach(function (m, i) {
      var am = T.amb.filter(function (x) { return x[0] === m[0] && x[1] === m[1]; })[0], bnd = 1 / (2 * m[0] * (m[0] + 1) * Ilen),
          q2 = (m[0] + 1) * m[1] + m[0],   // the bound of Corollary 6.4(b) at this b (its limit is 3/(4a(a+1)|I|))
          bnd2 = (q2 - 1) / (m[0] * (m[0] + 1) * Ilen) * ((q2 + 1) * Math.log(1 + 1 / q2) - (2 * q2 - 1) * Math.log(1 + 1 / (2 * q2 - 1)));
      table += '<tr style="color:#222;background:' + (m[0] === 2 ? CAT.E : CAT.Eb) + '"><td>' + m[0] + '</td><td>' + m[1] + '</td><td>' + m[2].toFixed(4) + (m[2] > bnd2 ? ' ✓' : ' ✗') + '</td><td>' + bnd.toFixed(4) +
        '</td><td>' + bnd2.toFixed(4) + '</td><td>' + (am ? (am[2] / am[3]).toFixed(4) : '–') + '</td></tr>';
      if (!(m[2] > bnd2)) bad = true;
    });
    table += '</table></div><p style="font-size:.9em">The means of Corollary 6.4 from the paper’s logs (quadratures over 600 values of θ, exact up to the sampling of θ) against the limit of bound (a) and the bound (b) at the same b; the interval I = [0.14, 6.9] contains [(2a−1)/(2a(a+1)), 1/a] for a = 2, 3, so (b) applies; ' +
      sw(CAT.E) + sw(CAT.Eb) + ' exact computation (the shades separate a = 2 and a = 3). The limit of the mean is open.</p>';
    return { text: text, fig3d: [spec], plots: [liveSvg], bad: bad, table: table,
             csv: { name: 'tent-section-a' + a + '-b' + b + '.csv', head: ['theta', 'd', 'A_num', 'A_den', 'A', 'bound'],
                    rows: live.map(function (x) { return [x.th, x.d, x.num, x.den, x.v, x.bound === null ? '' : x.bound]; }) } };
  }
  function flatTent(f) {
    var T = D.tent, bb = T.bs[f], q = 3 * bb + 2;
    var pts = T.ks.map(function (k, j) { return [k / T.den, T.Z[f][j]]; });
    var bnd = [];
    for (var t = 0; t <= 20; t++) { var d = t / 20 / 6; bnd.push([1 / 3 + d, 1 - 6 * d - 1 / q]); }
    return fig('2D view: the section at b = ' + bb + ' (follows the slider)', plot({ title: 'A₂,' + bb + '(θ), exact (θ = k/720)', x0: 0.15, x1: 0.85, y0: 0, y1: 1.02,
      xt: [0.2, 0.25, 0.333, 0.5, 0.667, 0.75, 0.85], yt: [0, 0.25, 0.5, 0.75, 1], xl: 'θ', yl: 'A',
      series: [{ pts: pts, color: ACCENT, width: 1.6, name: 'exact section, a = 2' }, { pts: bnd, color: '#333', dash: true, name: 'F₂(d) − 1/q, q = ' + q },
               { pts: [[1 / 3, 0], [1 / 3, 1]], color: PURPLE, width: 1, name: 'θ = 1/3' }], legend: true }));
  }
  function randomTent() { var a = 2 + Math.floor(Math.random() * 3); return { a: String(a), b: String(2 + Math.floor(Math.random() * (BMAXT[a] - 1))) }; }

  // =========================================================================================== 4. the torus
  function remainder30(b, W) { return 30 * W - 438 * b * b - 253 * b; }   // 30·r(b), r = W − 73/5 b² − 253/30 b
  function RalekN(a, b) {   // Number version (exact while V < 2^53; for a = 3, b ≤ 1000 far below)
    var m = 2 * b, n = 2 * a, V = 0;
    for (var i = 1; i <= m; i++) for (var j = 1; j <= n; j++) if (N.gcd(i, j) === 1) V += (m + 1 - i) * (n + 1 - j);
    return 1 + a + b + 2 * a * b + V / 2;
  }
  var TORUS = null;
  function torusData() {
    if (TORUS) return TORUS;
    var data = D.rows[3].filter(function (r) { return r[0] >= 5; }), cls = {}, okData = true;
    data.forEach(function (r) {
      var b = r[0], R = r[1], W = r[2];
      if (R - N.E3conj(b) !== W) okData = false;
      (cls[b % 60] = cls[b % 60] || {})[remainder30(b, W)] = 1;
    });
    var periodic60 = Object.keys(cls).length === 60 && Object.keys(cls).every(function (k) { return Object.keys(cls[k]).length === 1; });
    var notSmaller = [12, 15, 20, 30].every(function (d) {
      var c = {};
      data.forEach(function (r) { (c[r[0] % d] = c[r[0] % d] || {})[remainder30(r[0], r[2])] = 1; });
      return Object.keys(c).some(function (k) { return Object.keys(c[k]).length > 1; });
    });
    var r60 = {};
    Object.keys(cls).forEach(function (k) { r60[k] = +Object.keys(cls[k])[0]; });
    var formulaOk = true;
    for (var b = 5; b <= 1000; b++) { var Wf = RalekN(3, b) - N.E3conj(b); if (remainder30(b, Wf) !== r60[b % 60]) formulaOk = false; }
    var lo = Math.min.apply(null, Object.values(r60)), hi = Math.max.apply(null, Object.values(r60));
    TORUS = { data: data, r60: r60, periodic60: periodic60, notSmaller: notSmaller, okData: okData, formulaOk: formulaOk, lo: lo, hi: hi };
    return TORUS;
  }
  function torusPos(t, dr) {
    var u = 2 * Math.PI * t / 12, w = 2 * Math.PI * t / 5, RM = 3, rr = 1.1 + (dr || 0);
    return [(RM + rr * Math.cos(w)) * Math.cos(u) / 4.2, (RM + rr * Math.cos(w)) * Math.sin(u) / 4.2, rr * Math.sin(w) / 4.2];
  }
  function runTorus(v) {
    var b = intIn(v.b, 5, 1000);
    if (b === null) return { error: 'b must be an integer from 5 to 1000 (the conjectural formula holds from b = 5).' };
    var TD = torusData(), colr = function (k) { return ramp((TD.r60[k] - TD.lo) / Math.max(1, TD.hi - TD.lo)); };
    var R = N.Ralek(3, b), E = N.E3conj(b), W = R - BigInt(E), r30 = remainder30(b, Number(W));
    var dat = TD.data.filter(function (x) { return x[0] === b; })[0];
    var bad = !TD.periodic60 || !TD.notSmaller || !TD.okData || !TD.formulaOk || (dat && BigInt(dat[2]) !== W) || r30 !== TD.r60[b % 60];
    var grid = [];
    for (var i = 0; i <= 48; i++) {
      var row = [];
      for (var j = 0; j <= 24; j++) {
        var u = 2 * Math.PI * i / 48, w = 2 * Math.PI * j / 24;
        row.push([(3 + 1.1 * Math.cos(w)) * Math.cos(u) / 4.2, (3 + 1.1 * Math.cos(w)) * Math.sin(u) / 4.2, 1.1 * Math.sin(w) / 4.2]);
      }
      grid.push(row);
    }
    var knot = [];
    for (var t = 0; t <= 600; t++) knot.push(torusPos(t / 10, 0.02));
    var pts = [], cs = [];
    for (var k = 0; k < 60; k++) { pts.push(torusPos(k, 0.06)); cs.push(colr(k)); }
    var fixed = [{ type: 'surface', grid: grid, color: '#c9d1d6', opacity: 0.18 },
                 { type: 'curve', points: knot, color: '#7A8A99', width: 1, name: 'the (12,5) torus knot: b ↦ b+1' },
                 { type: 'points', points: pts, colors: cs, color: '#444', size: 6, name: 'the 60 residues of b, coloured by r(b)' }];
    var vals = [];
    for (var f = 0; f < 60; f++) vals.push(b + f);
    var frames = vals.map(function (bb) { return [{ type: 'points', points: [torusPos(bb % 60, 0.12)], color: '#000000', marker: 'star', size: 12, name: 'b at the slider' }]; });
    var spec = { title: 'W(3,b) modulo 60 on a torus (12 steps around, 5 through) · drag to turn', axes: ['', '', ''], items: fixed,
                 colorbar: { label: 'r(b) = W(3,b) − 73/5·b² − 253/30·b', stops: [[frac(TD.lo, 30), ramp(0)], [frac(Math.round((TD.lo + TD.hi) / 2), 30), ramp(0.5)], [frac(TD.hi, 30), ramp(1)]] },
                 slider: { label: 'b', values: vals, start: 0, items: frames }, flat: function (ff) { return flatTorus(vals[ff], colr, TD); } };
    var text = 'b = ' + b + ': R(3,b) = ' + R + ' (Alekseyev’s formula, exact), E(3,b) = ' + E + ' by the conjectural formula of Conjecture 9.8, W = R − E = ' + W +
      (dat ? (BigInt(dat[2]) === W ? ' = the exact enumeration of the paper ✓' : ' ≠ the exact enumeration (' + dat[2] + ') ✗') : ' (no exact enumeration at this b: formula only)') +
      '. r(b) = W − 73/5·b² − 253/30·b = ' + frac(r30, 30) + (r30 === TD.r60[b % 60] ? ', the value of its class b ≡ ' + (b % 60) + ' (mod 60) ✓' : ' ✗') + '. ' +
      'In the ' + TD.data.length + ' exact values of W(3,b), 5 ≤ b ≤ 300: W = R − (conjectural E) in all ' + (TD.okData ? '✓' : '✗') + '; r(b) depends only on b mod 60 ' + (TD.periodic60 ? '✓' : '✗') +
      ' and not only on b modulo 12, 15, 20 or 30 ' + (TD.notSmaller ? '✓' : '✗') + '; the formula gives the same 60 values for every 5 ≤ b ≤ 1000 ' + (TD.formulaOk ? '✓' : '✗') +
      '. b ≡ ' + (b % 12) + ' (mod 12), b ≡ ' + (b % 5) + ' (mod 5): one point of ℤ/12 × ℤ/5. This is an observation on the exact values and a property of the conjectural formula, not a theorem about W(3,b).';
    var table = '<div class="dk-tablewrap"><table class="dk-table"><tr style="background:' + CAT.head + '"><th>b mod 60</th><th>b mod 12</th><th>b mod 5</th><th>h_{b mod 4}</th><th>r(b)</th><th>exact values in the class</th></tr>';
    for (k = 0; k < 60; k++) {
      var n = TD.data.filter(function (x) { return x[0] % 60 === k; }).length, dark = k % 4 === 3;
      table += '<tr style="color:#222;background:' + (dark ? CAT.Qb : CAT.Q) + (k === b % 60 ? ';outline:2px solid #222;outline-offset:-2px;font-weight:700' : '') + '"><td>' + k + '</td><td>' + k % 12 + '</td><td>' + k % 5 +
        '</td><td>' + [0, 1, -1, 17][k % 4] + '</td><td>' + sw(colr(k)) + ' ' + frac(TD.r60[k], 30) + '</td><td>' + n + '</td></tr>';
    }
    table += '</table></div><p style="font-size:.9em">' + sw(CAT.Q) + sw(CAT.Qb) + ' the paper’s colour of a conjecture; the darker rows are b ≡ 3 (mod 4), where h jumps to 17. Your class is outlined.</p>';
    return { text: text, fig3d: [spec], plots: [], bad: bad, table: table,
             csv: { name: 'W3-mod-60.csv', head: ['b_mod_60', 'r_times_30'], rows: Object.keys(TD.r60).map(function (k2) { return [k2, TD.r60[k2]]; }) } };
  }
  function flatTorus(b, colr, TD) {
    var W = 520, H = 262, L = 60, T = 48, cw = (W - L - 16) / 12, ch = (H - T - 30) / 5;
    var out = [svgOpen(W, H + 10, 'flat torus')];
    out.push('<text x="' + W / 2 + '" y="18" text-anchor="middle" font-size="13" font-weight="700">the flat torus ℤ/12 × ℤ/5 (follows the slider: b = ' + b + ')</text>');
    for (var k = 0; k < 60; k++) {
      var x = L + (k % 12) * cw, y = T + (k % 5) * ch, sel = k === b % 60;
      out.push('<rect x="' + x.toFixed(1) + '" y="' + y.toFixed(1) + '" width="' + (cw - 2).toFixed(1) + '" height="' + (ch - 2).toFixed(1) + '" fill="' + colr(k) + '"' + (sel ? ' stroke="#000" stroke-width="3"' : '') + '/>');
      out.push('<text x="' + (x + cw / 2 - 1).toFixed(1) + '" y="' + (y + ch / 2 + 4).toFixed(1) + '" text-anchor="middle" font-size="10" fill="' + ((TD.r60[k] - TD.lo) / Math.max(1, TD.hi - TD.lo) > 0.6 ? '#222' : '#fff') + '">' + k + '</text>');
    }
    for (k = 0; k < 12; k++) out.push('<text x="' + (L + k * cw + cw / 2).toFixed(1) + '" y="' + (T - 6) + '" text-anchor="middle" font-size="11">' + k + '</text>');
    for (k = 0; k < 5; k++) out.push('<text x="' + (L - 8) + '" y="' + (T + k * ch + ch / 2 + 4).toFixed(1) + '" text-anchor="end" font-size="11">' + k + '</text>');
    out.push('<text x="' + (L + 6 * cw) + '" y="' + (H + 4) + '" text-anchor="middle" font-size="12" font-style="italic">b mod 12 (columns) · b mod 5 (rows) · each cell: b mod 60</text>');
    out.push('</svg>');
    return fig('2D view: the flat torus, same colours', out.join(''));
  }
  function randomTorus() { return { b: String(5 + Math.floor(Math.random() * 996)) }; }

  // ================================================================================================= wiring
  var LABS = { rigid: { run: runRigid, random: randomRigid },
               cert: { run: function (v) { return window.CertLab.run(v); }, random: function () { return window.CertLab.random(); } },
               boundary: { run: function (v) { return window.BoundaryLab.run(v); }, random: function () { return window.BoundaryLab.random(); } },
               cells: { run: runCells, random: randomCells },
               tent: { run: runTent, random: randomTent }, torus: { run: runTorus, random: randomTorus } };

  function slots3d(specs) {
    return [].concat(specs || []).map(function (_, k) {
      return '<div class="dk-pair" data-k="' + k + '"><div class="dk-3d" data-k="' + k + '"></div><div class="dk-2d" data-k="' + k + '"></div></div>';
    }).join('');
  }
  function mount3d(box, specs) {
    [].concat(specs || []).forEach(function (spec, k) {
      var el = box.querySelector('.dk-3d[data-k="' + k + '"]');
      if (!el || !spec) return;
      var kind = (window.LemmarioFigures || {})['3d'];
      if (!kind) { el.textContent = 'The 3D figure needs labjs/lab3d.js, which did not load.'; return; }
      kind.mount(el, spec);
      var el2 = box.querySelector('.dk-2d[data-k="' + k + '"]');
      if (!el2 || !spec.flat) return;
      var range = el.querySelector('input[type=range]'), val = el.querySelector('.l3-val'), last = -1;
      function redraw() {
        var f = range ? Number(range.value) : 0;
        if (f !== last) { last = f; el2.innerHTML = spec.flat(f); }
      }
      redraw();
      if (range) range.addEventListener('input', redraw);
      if (val && window.MutationObserver) new MutationObserver(redraw).observe(val, { childList: true, characterData: true, subtree: true });
    });
  }
  function values(box) {
    var v = {};
    box.querySelectorAll('[data-dk-in]').forEach(function (el) { v[el.getAttribute('data-dk-in')] = el.value; });
    return v;
  }
  function setValues(box, v) {
    Object.keys(v).forEach(function (k) { var el = box.querySelector('[data-dk-in="' + k + '"]'); if (el) el.value = v[k]; });
  }
  function tools(box, res) {
    var p = document.createElement('p');
    p.className = 'lm-tools';
    p.innerHTML = (res.csv ? '<button type="button" class="lm-csv">⬇ table as CSV</button> ' : '') +
      '<button type="button" class="lm-link">🔗 copy a link with these values</button> <span class="lm-toolmsg"></span>';
    var msg = p.querySelector('.lm-toolmsg'), csvb = p.querySelector('.lm-csv'), node = box.getAttribute('data-dk-node') || '';
    if (csvb) csvb.addEventListener('click', function () {
      var q = function (x) { x = String(x); return /[",\n]/.test(x) ? '"' + x.replace(/"/g, '""') + '"' : x; };
      var text = [res.csv.head].concat(res.csv.rows).map(function (r) { return r.map(q).join(','); }).join('\n');
      var a = document.createElement('a');
      a.href = URL.createObjectURL(new Blob([text + '\n'], { type: 'text/csv' }));
      a.download = res.csv.name || 'lab.csv';
      document.body.appendChild(a); a.click(); a.remove();
    });
    p.querySelector('.lm-link').addEventListener('click', function () {
      var url = location.href.split(/[?#]/)[0] + '?' + new URLSearchParams(Object.assign({ lab: node }, values(box))) + '#' + node;
      msg.setAttribute('data-url', url);
      var shown = function () {
        msg.innerHTML = '<input type="text" readonly size="40" value="' + esc(url).replace(/"/g, '&quot;') + '">';
        msg.querySelector('input').select();
      };
      if (navigator.clipboard && window.isSecureContext) navigator.clipboard.writeText(url).then(function () { msg.textContent = '✓ copied'; }, shown);
      else shown();
    });
    return p;
  }
  function show(box, lab) {
    // the result panels may have been emptied from outside (labweb clears .lm-out before each run): rebuild them
    var out = box.querySelector('.dk-out');
    if (out && !out.querySelector('.dk-text')) {
      out.innerHTML = '<div class="dk-plots lm-figs" data-lm-out></div><p class="dk-text" data-lm-out></p><div class="dk-tab" data-lm-out></div>';
    }
    var st = box.querySelector('.dk-status'), text = box.querySelector('.dk-text'), state = box.querySelector('.lm-state'),
        plots = box.querySelector('.dk-plots'), tab = box.querySelector('.dk-tab');
    st.className = 'dk-status'; st.textContent = 'Computing…';
    if (state) state.textContent = '⏳ computing…';
    var t0 = performance.now(), res;
    try { res = lab.run(values(box)); } catch (e) { res = { error: 'The computation failed: ' + (e && e.message || e) }; }
    var secs = ((performance.now() - t0) / 1000).toFixed(1);
    if (res.error) {
      st.className = 'dk-status err'; st.textContent = '⚠️ ' + res.error;
      if (state) state.textContent = '';
      text.textContent = ''; plots.innerHTML = ''; tab.innerHTML = '';
      return;
    }
    if (state) state.textContent = '✅ computed in ' + secs + ' s';
    st.textContent = res.bad ? '⚠️ Done, but a check FAILED (see below).' : '✅ Every check passed (exact integer arithmetic, in your browser).';
    if (res.bad) st.className = 'dk-status err';
    plots.innerHTML = slots3d(res.fig3d) + (res.plots || []).join('');
    mount3d(plots, res.fig3d);
    text.textContent = res.text;
    tab.innerHTML = res.table || '';
    tab.appendChild(tools(box, res));
  }
  function openLab(box) {
    for (var e = box; e; e = e.parentElement) if (e.tagName === 'DETAILS') e.open = true;
    box.scrollIntoView({ block: 'start' });
  }
  function wire(box) {
    var lab = LABS[box.getAttribute('data-dk-lab')];
    if (!lab) return;
    var go = function () { setTimeout(function () { show(box, lab); }, 0); };
    var run = box.querySelector('.dk-run');
    if (run) run.addEventListener('click', go);
    box.querySelectorAll('.dk-random').forEach(function (rnd) {
      rnd.addEventListener('click', function () { setValues(box, lab.random()); go(); });
    });
    var P = new URLSearchParams(location.search), linked = P.get('lab') === box.getAttribute('data-dk-node');
    if (linked) box.querySelectorAll('[data-dk-in]').forEach(function (el) {
      var k = el.getAttribute('data-dk-in');
      if (P.has(k)) el.value = P.get(k);
    });
    box.querySelectorAll('[data-dk-example]').forEach(function (btn) {
      btn.addEventListener('click', function () { setValues(box, JSON.parse(btn.getAttribute('data-dk-example'))); go(); });
    });
    box.querySelectorAll('[data-dk-in]').forEach(function (el) {
      el.addEventListener('keydown', function (e) { if (e.key === 'Enter') { e.preventDefault(); go(); } });
      if (el.tagName === 'SELECT') el.addEventListener('change', go);
    });
    show(box, lab);
    if (linked) setTimeout(function () { openLab(box); }, 300);
  }
  function start() {
    if (!N) throw new Error('nucleo.js did not load (window.RigidNucleo is missing)');
    if (!D) throw new Error('datos.js did not load (window.RigidDatos is missing)');
    document.querySelectorAll('[data-dk-lab]').forEach(wire);
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
