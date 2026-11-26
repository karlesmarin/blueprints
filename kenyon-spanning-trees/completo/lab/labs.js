// encaje: interfaz del lab JS del blueprint kenyon-spanning-trees (formulario, ejemplos, aleatorio, 3D, SVG, tabla);
// la aritmética está en nucleo.js y los datos en datos.js (generado de extremal_graphs.json). Lo instala
// excovery.lemmario.labjs (engine = 'js'); sin red, sirve desde file://. Mirado: Lemmario (lo instala, no trae la
// interfaz de un lab JS), labweb (lo prueba en Chrome) y dyck-divisors/labjs/labs.js (mismo cableado; otra figura).
/* The lab «The extremal multigraphs in 3D»: a <div data-dk-lab="graphs"> written by lab_graphs.html; its result panels
   carry data-lm-out. It computes its default input as soon as the script runs (no click needed). */
(function () {
  'use strict';
  var N = window.KenyonNucleo, D = window.KenyonDatos;
  // the paper's colour code (Okabe-Ito): blue = certified, vermilion = search only, purple = multiple edge
  var AZUL = '#0072B2', BERMELLON = '#D55E00', PURPURA = '#CC79A7', GRIS = '#7A8A99';
  var DEG_COL = { 1: '#56B4E9', 2: '#999999', 3: '#009E73', 4: '#E69F00', 5: '#000000', 6: '#000000' };
  function degCol(d) { return DEG_COL[d] || '#000000'; }
  var CLS = { T: 'T(m): all loopless multigraphs', S: 'S(m): simple graphs', M: 'M(m): multigraphs with a multiple edge' };

  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }
  function sup(n) { return String(n).split('').map(function (c) { return '⁰¹²³⁴⁵⁶⁷⁸⁹'[+c]; }).join(''); }
  function degWord(deg) { return N.degreeWord(deg).map(function (p) { return p[0] + sup(p[1]); }).join(' '); }
  function row(m) { return D.rows[m - 1]; }
  function status(r) { return r.status === 'certificate' ? 'certified (Theorem 2)' : 'exhaustive search only (Computational result 3)'; }
  function stCol(r) { return r.status === 'certificate' ? AZUL : BERMELLON; }

  /* Everything checked about one graph, exactly: τ by Kirchhoff (BigInt), its m, degrees, and the trees through
     each copy, whose sum must be (n − 1)·τ. Cached: the slider shows every m. */
  var CACHE = {};
  function analyse(r, cls, i) {
    var key = r.m + cls + i;
    if (CACHE[key]) return CACHE[key];
    var g = r[cls + '_ext'][i], t = N.tau(g.n, g.e), deg = N.degrees(g.n, g.e);
    var through = N.treesThrough(g.n, g.e, t), sum = 0n;
    g.e.forEach(function (e, k) { sum += BigInt(e[2]) * through[k]; });
    var degSorted = deg.slice().sort(function (a, b) { return b - a; });
    var a = { g: g, tau: t, deg: deg, through: through,
              okTau: String(t) === String(g.tau) && String(t) === String(r[cls]),
              okM: g.e.reduce(function (s, e) { return s + e[2]; }, 0) === r.m,
              okDeg: JSON.stringify(degSorted) === JSON.stringify(g.deg),
              okSum: sum === BigInt(g.n - 1) * t,
              pos: N.layout3d(g.n, g.e) };
    a.ok = a.okTau && a.okM && a.okDeg && a.okSum;
    CACHE[key] = a;
    return a;
  }

  // ------------------------------------------------------------------------------------------------ the 3D figure
  function sub(p, q) { return [p[0] - q[0], p[1] - q[1], p[2] - q[2]]; }
  function cross(u, v) { return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]; }
  function norm(u) { var l = Math.hypot(u[0], u[1], u[2]) || 1; return [u[0] / l, u[1] / l, u[2] / l]; }

  /* One graph as lab3d items: vertices coloured by degree, each edge copy a curve (the copies of a multiple edge bow
     apart, in purple), the width of a copy growing with the share of spanning trees through it. */
  function graphItems(a, shift, scale, named) {
    var P = a.pos.map(function (p) { return [p[0] * scale + shift, p[1] * scale, p[2] * scale]; });
    var items = [], T = Number(a.tau), seen = {};
    a.g.e.forEach(function (e, k) {
      var u = P[e[0]], v = P[e[1]], mid = [(u[0] + v[0]) / 2, (u[1] + v[1]) / 2, (u[2] + v[2]) / 2];
      var dir = sub(v, u), side = cross(dir, sub(mid, [shift, 0, 0]));
      if (Math.hypot(side[0], side[1], side[2]) < 1e-6) side = cross(dir, [0, 0, 1]);
      if (Math.hypot(side[0], side[1], side[2]) < 1e-6) side = cross(dir, [0, 1, 0]);
      side = norm(side);
      var len = Math.hypot(dir[0], dir[1], dir[2]), share = Number(a.through[k]) / T;
      var multi = e[2] > 1, col = multi ? PURPURA : GRIS, width = 1.2 + 4.5 * share;
      for (var c = 0; c < e[2]; c++) {
        var off = (c - (e[2] - 1) / 2) * 0.22 * len, pts = [];
        for (var s = 0; s <= 12; s++) {
          var t = s / 12, b = 4 * t * (1 - t) * off;
          pts.push([u[0] + t * dir[0] + side[0] * b, u[1] + t * dir[1] + side[1] * b, u[2] + t * dir[2] + side[2] * b]);
        }
        var kind = multi ? 'multi' : 'single', it = { type: 'curve', points: pts, color: col, width: width };
        if (named && !seen[kind]) {
          it.name = multi ? 'copies of a multiple edge (×' + e[2] + ')' : 'simple edge (thicker: more spanning trees use it)';
          seen[kind] = 1;
        }
        items.push(it);
      }
    });
    var byDeg = {};
    a.deg.forEach(function (d, i) { (byDeg[d] = byDeg[d] || []).push(P[i]); });
    Object.keys(byDeg).map(Number).sort().forEach(function (d) {
      items.push({ type: 'points', points: byDeg[d], color: degCol(d), size: 7,
                   name: named ? 'degree ' + d + (named === 'one' ? ' (' + byDeg[d].length + ' vertices)' : '') : undefined });
    });
    return items;
  }

  function frameItems(m, cls) {
    var r = row(m), list = r[cls + '_ext'], k = list.length, items = [];
    list.forEach(function (_, i) {
      var a = analyse(r, cls, i);
      var scale = k === 1 ? 1 : 0.62, shift = k === 1 ? 0 : (i - (k - 1) / 2) * 1.45;
      // legend: the first graph names every kind (with vertex counts when it is alone); the others add the degrees
      // the first one does not have
      var named = i === 0 ? (k === 1 ? 'one' : 'many') : false, its = graphItems(a, shift, scale, k === 1 ? 'one' : 'many');
      its.forEach(function (it) {
        if (it.name && !named && items.some(function (o) { return o.name === it.name; })) delete it.name;
      });
      items = items.concat(its);
    });
    return items;
  }

  // ------------------------------------------------------------------------------------------- the 2D companion
  /* The same graph(s) drawn flat: vertices on a circle (labels 0..n−1 as in the data file), multiple edges as purple
     arcs with ×k, vertices coloured by degree; underneath, the status of the row of Table 1. */
  function flat(m, cls) {
    var r = row(m), list = r[cls + '_ext'], W = 360, H0 = 335, k = list.length;
    var out = ['<svg class="dk-svg" viewBox="0 0 ' + W + ' ' + (H0 + 96) + '" role="img" aria-label="m = ' + m + ', flat drawing">'];
    out.push('<text x="' + W / 2 + '" y="18" text-anchor="middle" font-size="13" font-weight="700">m = ' + m + ' · ' +
             esc(cls) + '(' + m + ') = ' + (r[cls] === null ? '—' : r[cls]) + ' · ' + (k === 1 ? 'one extremizer' : k + ' extremizers') + '</text>');
    list.forEach(function (g, i) {
      var a = analyse(r, cls, i), cx = k === 1 ? W / 2 : W * (i + 0.5) / k, cy = 160, R = k === 1 ? 105 : 62;
      var P = [];
      for (var v = 0; v < g.n; v++) {
        var ang = -Math.PI / 2 + 2 * Math.PI * v / g.n;
        P.push([cx + R * Math.cos(ang), cy + R * Math.sin(ang)]);
      }
      g.e.forEach(function (e) {
        var p = P[e[0]], q = P[e[1]];
        if (e[2] === 1) {
          out.push('<line x1="' + p[0].toFixed(1) + '" y1="' + p[1].toFixed(1) + '" x2="' + q[0].toFixed(1) + '" y2="' + q[1].toFixed(1) +
                   '" stroke="' + GRIS + '" stroke-width="1.6"/>');
          return;
        }
        var dx = q[0] - p[0], dy = q[1] - p[1], L = Math.hypot(dx, dy) || 1, nx = -dy / L, ny = dx / L;
        for (var c = 0; c < e[2]; c++) {
          var off = (c - (e[2] - 1) / 2) * 0.45 * L, mx = (p[0] + q[0]) / 2 + nx * off, my = (p[1] + q[1]) / 2 + ny * off;
          out.push('<path d="M' + p[0].toFixed(1) + ',' + p[1].toFixed(1) + ' Q' + mx.toFixed(1) + ',' + my.toFixed(1) + ' ' +
                   q[0].toFixed(1) + ',' + q[1].toFixed(1) + '" fill="none" stroke="' + PURPURA + '" stroke-width="2.4"/>');
        }
        var lx = (p[0] + q[0]) / 2 + nx * (0.3 * L + 10), ly = (p[1] + q[1]) / 2 + ny * (0.3 * L + 10);
        out.push('<text x="' + lx.toFixed(1) + '" y="' + (ly + 4).toFixed(1) + '" text-anchor="middle" font-size="12" font-weight="700" fill="' +
                 PURPURA + '">×' + e[2] + '</text>');
      });
      P.forEach(function (p, v) {
        out.push('<circle cx="' + p[0].toFixed(1) + '" cy="' + p[1].toFixed(1) + '" r="10" fill="' + degCol(a.deg[v]) + '" stroke="#fff" stroke-width="1.5"/>');
        out.push('<text x="' + p[0].toFixed(1) + '" y="' + (p[1] + 4).toFixed(1) + '" text-anchor="middle" font-size="11" fill="#fff" font-weight="700">' + v + '</text>');
      });
      out.push('<text x="' + cx + '" y="' + (cy + R + 30) + '" text-anchor="middle" font-size="12">n = ' + g.n + ', τ = ' + a.tau +
               (a.ok ? ' ✓' : ' ✗') + '</text>');
      out.push('<text x="' + cx + '" y="' + (cy + R + 46) + '" text-anchor="middle" font-size="12">degrees ' + esc(degWord(a.deg)) + '</text>');
    });
    var y = H0 + 22;
    out.push('<rect x="8" y="' + (y - 14) + '" width="' + (W - 16) + '" height="22" fill="' + (r.status === 'certificate' ? D.tints.C0 : D.tints.E0) +
             '" stroke="' + stCol(r) + '"/>');
    out.push('<text x="' + W / 2 + '" y="' + (y + 1) + '" text-anchor="middle" font-size="12" fill="' + stCol(r) + '" font-weight="700">' +
             (r.status === 'certificate' ? 'C · certified (Theorem 2)' : 'E · exhaustive search only (Result 3)') + '</text>');
    out.push('<text x="' + W / 2 + '" y="' + (y + 30) + '" text-anchor="middle" font-size="12">vertex colour = degree:</text>');
    var degs = [2, 3, 4, 5], x0 = W / 2 - 100;
    degs.forEach(function (d, j) {
      out.push('<circle cx="' + (x0 + j * 62) + '" cy="' + (y + 48) + '" r="7" fill="' + degCol(d) + '"/>');
      out.push('<text x="' + (x0 + j * 62 + 11) + '" y="' + (y + 52) + '" font-size="12">' + d + (d === 5 ? '+' : '') + '</text>');
    });
    out.push('<text x="' + W / 2 + '" y="' + (y + 70) + '" text-anchor="middle" font-size="12" fill="' + PURPURA + '">purple arcs: a multiple edge</text>');
    out.push('</svg>');
    return '<figure class="dk-fig"><figcaption>Flat view (follows the slider)</figcaption>' + out.join('') + '</figure>';
  }

  // --------------------------------------------------------------------------------- T(m)^(1/m) against sqrt(27/8)
  function growthPlot(mSel) {
    var W = 520, H = 300, L = 52, Rr = 14, Tp = 30, B = 44, lo = 1.0, hi = 1.9;
    function X(m) { return L + (m - 1) / 21 * (W - L - Rr); }
    function Y(v) { return Tp + (hi - v) / (hi - lo) * (H - Tp - B); }
    var out = ['<svg class="dk-svg" viewBox="0 0 ' + W + ' ' + (H + 40) + '" role="img" aria-label="T(m) to the power 1/m">'];
    out.push('<text x="' + W / 2 + '" y="16" text-anchor="middle" font-size="13" font-weight="700">T(m)^(1/m) for m = 1, …, 22 (Remark 4(3))</text>');
    for (var j = 0; j <= 9; j++) {
      var v = 1 + j / 10;
      out.push('<line x1="' + L + '" x2="' + (W - Rr) + '" y1="' + Y(v).toFixed(1) + '" y2="' + Y(v).toFixed(1) + '" stroke="#e3e7eb"/>');
      out.push('<text x="' + (L - 6) + '" y="' + (Y(v) + 4).toFixed(1) + '" text-anchor="end" font-size="11">' + v.toFixed(1) + '</text>');
    }
    [1, 4, 8, 12, 16, 20, 22].forEach(function (m) {
      out.push('<text x="' + X(m).toFixed(1) + '" y="' + (H - B + 16) + '" text-anchor="middle" font-size="11">' + m + '</text>');
    });
    out.push('<text x="' + ((L + W) / 2) + '" y="' + (H - B + 32) + '" text-anchor="middle" font-size="12" font-style="italic">m (number of edges)</text>');
    var c = Math.sqrt(27 / 8);
    out.push('<line x1="' + L + '" x2="' + (W - Rr) + '" y1="' + Y(c).toFixed(1) + '" y2="' + Y(c).toFixed(1) + '" stroke="#555" stroke-dasharray="6 4"/>');
    var path = [];
    D.rows.forEach(function (r) { path.push((path.length ? 'L' : 'M') + X(r.m).toFixed(1) + ',' + Y(Math.pow(r.T, 1 / r.m)).toFixed(1)); });
    out.push('<path d="' + path.join(' ') + '" fill="none" stroke="#9aa6b2" stroke-width="1.2"/>');
    D.rows.forEach(function (r) {
      var y = Y(Math.pow(r.T, 1 / r.m)), x = X(r.m);
      if (r.m === mSel) out.push('<circle cx="' + x.toFixed(1) + '" cy="' + y.toFixed(1) + '" r="9" fill="none" stroke="#222" stroke-width="2"/>');
      out.push('<circle cx="' + x.toFixed(1) + '" cy="' + y.toFixed(1) + '" r="4.5" fill="' + stCol(r) + '"/>');
    });
    var ly = H + 2;
    out.push('<circle cx="' + (L + 6) + '" cy="' + ly + '" r="5" fill="' + AZUL + '"/><text x="' + (L + 16) + '" y="' + (ly + 4) + '" font-size="12">certified (m ≤ 18)</text>');
    out.push('<circle cx="' + (L + 150) + '" cy="' + ly + '" r="5" fill="' + BERMELLON + '"/><text x="' + (L + 160) + '" y="' + (ly + 4) + '" font-size="12">search only (19 ≤ m ≤ 22)</text>');
    out.push('<line x1="' + L + '" x2="' + (L + 14) + '" y1="' + (ly + 22) + '" y2="' + (ly + 22) + '" stroke="#555" stroke-dasharray="6 4"/>' +
             '<text x="' + (L + 20) + '" y="' + (ly + 26) + '" font-size="12">√(27/8) = 1.8371…, the optimal base (Majchrzak)</text>');
    out.push('</svg>');
    return '<figure class="dk-fig"><figcaption>Growth of T(m): the ringed point is your m</figcaption>' + out.join('') + '</figure>';
  }

  // ------------------------------------------------------------------------------------------- the coloured table
  function table(mSel) {
    // the paper's tints (accent!5 / !11, accent2!7 / !14, oipurple!32, accent!14), computed by lab/hacer_datos.py
    var tint = D.tints, purple = D.tints.M;
    var sw = function (c) { return '<span style="display:inline-block;width:1.1em;height:.8em;border:1px solid #888;vertical-align:middle;background:' + c + '"></span>'; };
    var h = '<div class="dk-tablewrap"><table class="dk-table"><tr style="background:' + D.tints.head + '"><th>m</th><th>T(m)</th><th>#ext.</th><th>n</th>' +
            '<th>S(m)</th><th>M(m)</th><th>status</th><th>τ in your browser</th></tr>';
    D.rows.forEach(function (r) {
      var okAll = true;
      ['T', 'S', 'M'].forEach(function (c) { r[c + '_ext'].forEach(function (_, i) { okAll = okAll && analyse(r, c, i).ok; }); });
      var bg = tint[(r.status === 'certificate' ? 'C' : 'E') + (r.m % 2 === 0 ? 1 : 0)];
      var multi = r.T_ext.some(function (g) { return !g.simple; });
      var ns = r.T_ext.map(function (g) { return g.n; }).filter(function (x, i, a) { return a.indexOf(x) === i; }).sort(function (a, b) { return a - b; }).join(', ');
      var sel = r.m === mSel ? ';outline:2px solid #222;outline-offset:-2px;font-weight:700' : '';
      var top = r.m === 19 ? ';border-top:2px solid #555' : '';
      h += '<tr style="color:#222;background:' + bg + sel + top + '"><td>' + r.m + '</td>' +
           (multi ? '<td style="background:' + purple + ';font-weight:700">' + r.T + '</td>' : '<td>' + r.T + '</td>') +
           '<td>' + r.T_ext.length + '</td><td>' + ns + '</td><td>' + r.S + '</td><td>' + (r.M === null ? '–' : r.M) + '</td>' +
           '<td style="color:' + stCol(r) + ';font-weight:700">' + (r.status === 'certificate' ? 'C' : 'E') + '</td>' +
           '<td>' + (okAll ? '✓ all ' + (r.T_ext.length + r.S_ext.length + r.M_ext.length) + ' graphs' : '✗ MISMATCH') + '</td></tr>';
    });
    h += '</table></div><p style="font-size:.9em">' + sw(tint.C0) + sw(tint.C1) + ' certified (C, Theorem 2) · ' + sw(tint.E0) + sw(tint.E1) +
         ' exhaustive search only (E, Computational result 3; below the thick rule) · ' + sw(purple) +
         ' <b>T(m)</b> in bold: some extremizer has a multiple edge. The last column recomputes τ of every listed extremizer of T, S and M ' +
         '(Kirchhoff, exact) and compares it with the file and the table. Your m is outlined.</p>';
    return h;
  }

  // ------------------------------------------------------------------------------------------------------ the lab
  function runGraphs(v) {
    var m = parseInt(v.m, 10), cls = String(v.cls || 'T').toUpperCase();
    if (!(m >= 1 && m <= 22) || String(m) !== String(v.m).trim()) return { error: 'm must be an integer from 1 to 22 (the range of the paper’s data).' };
    if (!CLS[cls]) return { error: 'the class must be T, S or M.' };
    if (cls === 'M' && m === 1) return { error: 'M(1) is undefined (Definition 1): with one edge there is no multiple edge.' };
    var r = row(m), list = r[cls + '_ext'], bad = false, parts = [];
    list.forEach(function (g, i) {
      var a = analyse(r, cls, i);
      bad = bad || !a.ok;
      var multi = g.e.filter(function (e) { return e[2] > 1; }).map(function (e) { return e[0] + '–' + e[1] + ' ×' + e[2]; });
      var shares = {};
      g.e.forEach(function (e, k) { var s = N.frac(a.through[k], a.tau); shares[s] = (shares[s] || 0) + e[2]; });
      parts.push((list.length > 1 ? 'Extremizer ' + (i + 1) + ' of ' + list.length + ': ' : 'The extremizer: ') +
        'n = ' + g.n + ' vertices, ' + (g.simple ? 'simple' : 'not simple (multiple edge ' + multi.join(', ') + ')') +
        ', degrees ' + degWord(a.deg) + ', graph6 of the skeleton ' + g.g6 + '. ' +
        'τ computed now by Kirchhoff’s theorem (determinant of the reduced Laplacian, exact BigInt arithmetic) = ' + a.tau +
        (a.okTau ? ' = the file and Table 1 ✓' : ' ≠ the file (' + g.tau + ') ✗') + '. ' +
        'Share of the spanning trees through one copy of each edge (by (K2), the effective resistance of its ends): ' +
        Object.keys(shares).map(function (s) { return s + ' (' + shares[s] + ' cop' + (shares[s] === 1 ? 'y' : 'ies') + ')'; }).join(', ') +
        '; their sum over all copies is n − 1 = ' + (g.n - 1) + (a.okSum ? ' ✓' : ' ✗') + '.');
    });
    var head = 'm = ' + m + ', class ' + CLS[cls] + ': ' + cls + '(' + m + ') = ' + r[cls] + ', ' + status(r) + '. ';
    var spec = {
      title: 'Drag to turn · the slider runs through m = 1, …, 22 (class ' + cls + ')',
      axes: ['', '', ''], zoomOut: 0,
      items: [],
      slider: { label: 'm', values: D.rows.map(function (x) { return x.m; }), start: m - 1,
                items: D.rows.map(function (x) { return (cls === 'M' && x.m === 1) ? [] : frameItems(x.m, cls); }) },
      flat: function (f) { var mm = f + 1; return (cls === 'M' && mm === 1) ? '<p>M(1) is undefined.</p>' : flat(mm, cls); }
    };
    return { text: head + parts.join(' '), fig3d: [spec], plots: [growthPlot(m)], bad: bad, table: table(m),
             csv: { head: ['m', 'T', 'S', 'M', 'status', 'n_extremizers_T'],
                    rows: D.rows.map(function (x) { return [x.m, x.T, x.S, x.M === null ? '' : x.M, x.status, x.T_ext.length]; }) } };
  }
  function randomGraphs() {
    var m = 2 + Math.floor(Math.random() * 21), c = ['T', 'T', 'S', 'M'][Math.floor(Math.random() * 4)];
    return { m: String(m), cls: c };
  }

  // ------------------------------------------------------------------------------------------------ the wiring
  var LABS = { graphs: { run: runGraphs, random: randomGraphs } };

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
      var zout = el.querySelector('.l3-zout');
      for (var i = 0; zout && i < (spec.zoomOut || 0); i++) zout.click();
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
      a.download = 'kenyon-T-m.csv';
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
      out.innerHTML = '<p class="dk-text" data-lm-out></p><div class="dk-plots lm-figs" data-lm-out></div><div class="dk-tab" data-lm-out></div>';
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
    st.textContent = res.bad ? '⚠️ Done, but a check FAILED (see below).' :
      '✅ Every check passed (exact integer arithmetic, in your browser).';
    if (res.bad) st.className = 'dk-status err';
    text.textContent = res.text;
    plots.innerHTML = slots3d(res.fig3d) + res.plots.join('');
    mount3d(plots, res.fig3d);
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
    if (!N) throw new Error('nucleo.js did not load (window.KenyonNucleo is missing)');
    if (!D) throw new Error('datos.js did not load (window.KenyonDatos is missing)');
    document.querySelectorAll('[data-dk-lab]').forEach(wire);
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
