// encaje: interfaz de los labs JS del blueprint dyck-divisors (formularios, ejemplos, aleatorio, texto, SVG, tabla);
// la aritmética está en nucleo.js. Lo instala excovery.lemmario.labjs (engine = 'js'); sin red, sirve desde file://.
// Mirados en el catálogo: Lemmario (lo instala, no trae la interfaz de un lab JS) y labweb (prueba labs Pyodide).
/* The two labs of the page: «Figure 1 live» (the word of n) and «Figure 7 live» (cells and words). Each lab box is a
   <div data-dk-lab="word|cells"> written by lab_word.html / lab_cells.html; the result panels carry data-lm-out.
   The labs compute their default inputs as soon as the script runs (no click needed). */
(function () {
  'use strict';
  var N = window.DyckNucleo;
  var AZUL = '#0072B2', NARANJA = '#E69F00', VERDE = '#009E73', GRIS = '#999999', BERMELLON = '#D55E00';
  var PALETTE = ['#1B6F8C', '#B5530F', '#2E7D32', '#6A1B9A', '#C62828', '#455A64'];
  var clipCount = 0;

  function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }
  function g3(v) {  // like Python '%.3g'
    if (v === 0) return '0';
    var s = Number(v).toPrecision(3);
    if (s.indexOf('e') < 0 && s.indexOf('.') >= 0) s = s.replace(/0+$/, '').replace(/\.$/, '');
    return s;
  }

  /* The legend of an SVG panel (25-nov, Carles: the text of the 2D panels was too small, the legends most): entries
     [[colour, text], ...]; two consecutive entries that each fit half the width in one line share a row, any other
     takes the whole width and wraps onto more lines if it needs to, so nothing leaves the frame. The width of a character is an
     estimate for Arial (the font of .dk-svg), on the generous side. Returns {svg: [...], height}. */
  function svgLegend(entries, x0, y0, width, fs) {
    var cw = 0.56 * fs, lh = Math.round(fs * 1.3), sw = 18;
    var half = (width - 12) / 2, out = [], y = y0, maxc;
    function fits(e) { return e && e[1].length * cw + sw <= half; }
    function wrap(s) {
      var lines = [], cur = '';
      s.split(' ').forEach(function (w) {
        if (cur && (cur + ' ' + w).length > maxc) { lines.push(cur); cur = w; } else cur = cur ? cur + ' ' + w : w;
      });
      if (cur) lines.push(cur);
      return lines;
    }
    for (var k = 0; k < entries.length; k += row.length) {
      // two short entries share a row; a long one takes the whole width (and wraps if it needs to)
      var two = fits(entries[k]) && fits(entries[k + 1]), row = entries.slice(k, k + (two ? 2 : 1)), hmax = 1;
      var colW = two ? half : width;
      maxc = Math.max(8, Math.floor((colW - sw) / cw));
      row.forEach(function (e, j) {
        var lx = x0 + j * (colW + 12), lines = wrap(e[1]);
        hmax = Math.max(hmax, lines.length);
        out.push('<rect x="' + lx.toFixed(1) + '" y="' + (y + lh / 2 - 5).toFixed(1) + '" width="12" height="8" fill="' + e[0] + '"/>');
        lines.forEach(function (ln, i) {
          out.push('<text x="' + (lx + sw).toFixed(1) + '" y="' + (y + lh / 2 + fs * 0.35 + i * lh).toFixed(1) + '" font-size="' + fs + '">' +
                   esc(ln) + '</text>');
        });
      });
      y += hmax * lh + 2;
    }
    return { svg: out, height: y - y0 };
  }

  /* Port of labkit.svg_plot: series [{name, x, y, mode: 'points'|'line', color, size}] -> SVG string.
     o.fs: the font size of the panel in its own units (25-nov: 13 by default, so that at the width it is shown the text
     reads like the page; a side panel passes a smaller o.width, which scales it up on screen). */
  function svgPlot(series, o) {
    o = o || {};
    var width = o.width || 560, height = o.height || 320, xs = [], ys = [], fs = o.fs || 13;
    series.forEach(function (s) { xs = xs.concat(s.x); ys = ys.concat(s.y); });
    if (!xs.length) return '<svg xmlns="http://www.w3.org/2000/svg"></svg>';
    var x0 = Math.min.apply(null, xs), x1 = Math.max.apply(null, xs), y0 = Math.min.apply(null, ys), y1 = Math.max.apply(null, ys);
    var py = 0.06 * ((y1 - y0) || Math.abs(y1) || 1);
    y0 -= py; y1 += py;
    var L = 62, R = 18, T = 16, B = 50;
    var legs = [];
    series.forEach(function (s, k) { if (s.name) legs.push([s.color || PALETTE[k % PALETTE.length], s.name]); });
    var LG = svgLegend(legs, 10, height + 2, width - 20, fs), H = height + LG.height + 6;
    function X(v) { return L + (v - x0) / ((x1 - x0) || 1) * (width - L - R); }
    function Y(v) { return height - B - (v - y0) / ((y1 - y0) || 1) * (height - T - B); }
    var clip = 'dkclip' + (++clipCount);
    var out = ['<svg viewBox="0 0 ' + width + ' ' + H + '" class="dk-svg" role="img" aria-label="' + esc(o.title || '') +
               '" xmlns="http://www.w3.org/2000/svg">',
               '<defs><clipPath id="' + clip + '"><rect x="' + (L - 6) + '" y="' + (T - 6) + '" width="' + (width - L - R + 12) +
               '" height="' + (height - T - B + 12) + '"/></clipPath></defs>'];
    for (var i = 0; i < 6; i++) {
      var v = y0 + (y1 - y0) * i / 5, y = height - B - (height - T - B) * i / 5;
      out.push('<line x1="' + L + '" x2="' + (width - R) + '" y1="' + y.toFixed(1) + '" y2="' + y.toFixed(1) + '" stroke="#eee"/>');
      out.push('<text x="' + (L - 5) + '" y="' + (y + 4).toFixed(1) + '" font-size="' + (fs - 1) + '" text-anchor="end">' + g3(v) + '</text>');
      var xv = x0 + (x1 - x0) * i / 5;
      out.push('<text x="' + (L + (width - L - R) * i / 5).toFixed(1) + '" y="' + (height - B + fs + 4) +
               '" font-size="' + (fs - 1) + '" text-anchor="middle">' + g3(xv) + '</text>');
    }
    out.push('<g clip-path="url(#' + clip + ')">');
    series.forEach(function (s, k) {
      var c = s.color || PALETTE[k % PALETTE.length];
      if (s.mode === 'line' && s.x.length > 1) {
        var d = s.x.map(function (x, j) { return X(x).toFixed(1) + ' ' + Y(s.y[j]).toFixed(1); }).join(' L');
        out.push('<path d="M' + d + '" fill="none" stroke="' + c + '" stroke-width="2"/>');
      } else {
        var r = s.size || 3;
        for (var j = 0; j < s.x.length; j++)
          out.push('<circle cx="' + X(s.x[j]).toFixed(1) + '" cy="' + Y(s.y[j]).toFixed(1) + '" r="' + r + '" fill="' + c + '" fill-opacity="0.65"/>');
      }
    });
    out.push('</g>');
    out.push('<text x="' + ((L + width - R) / 2) + '" y="' + (height - 8) + '" text-anchor="middle" font-size="' + fs + '">' + esc(o.xlabel || '') + '</text>');
    out.push('<text x="16" y="' + ((T + height - B) / 2) + '" font-size="' + fs + '" text-anchor="middle" transform="rotate(-90 16 ' +
             ((T + height - B) / 2) + ')">' + esc(o.ylabel || '') + '</text>');
    out = out.concat(LG.svg);
    out.push('</svg>');
    return '<figure class="dk-fig"><figcaption>' + esc(o.title || '') + '</figcaption>' + out.join('') + '</figure>';
  }

  function table(head, rows) {
    return '<div class="dk-tablewrap"><table class="dk-table"><thead><tr>' + head.map(function (h) { return '<th>' + esc(h) + '</th>'; }).join('') +
           '</tr></thead><tbody>' + rows.map(function (r) {
             return '<tr>' + r.map(function (c) { return '<td>' + esc(c) + '</td>'; }).join('') + '</tr>';
           }).join('') + '</tbody></table></div>';
  }

  function blog(x) { return Math.log(Number(x)); }  // drawing only: positions on the log line, never a check

  // ------------------------------------------------------------------------------------------------ the word lab
  function linePlot(n, m, t) {
    var Dm = N.divisors(m), lt = blog(t);
    var xs = Dm.map(function (d) { return blog(d) / lt; });
    var series = [{ name: 'divisors d of the odd part m: log d / log t (letters “(”)', x: xs, y: xs.map(function () { return 1; }),
                    mode: 'points', color: AZUL, size: 4 },
                  { name: 'partners t·d: log d / log t + 1 (letters “)”)', x: xs.map(function (x) { return x + 1; }),
                    y: xs.map(function () { return 0; }), mode: 'points', color: NARANJA, size: 4 }];
    xs.slice(0, 40).forEach(function (x) { series.push({ name: '', x: [x, x + 1], y: [1, 0], mode: 'line', color: '#DDDDDD' }); });
    return svgPlot(series, { title: 'n = ' + n + ': the divisors of m = ' + m + ' and their partners (t = ' + t + ')',
                             xlabel: 'position in units of log t', ylabel: '', height: 220 });
  }

  function pathPlot(w) {
    var hs = N.heights(w), idx = hs.map(function (_, i) { return i; });
    return svgPlot([{ name: 'Dyck path of the word (height after each letter)', x: idx, y: hs, mode: 'line', color: AZUL },
                    { name: '', x: idx, y: hs, mode: 'points', color: AZUL, size: 2.5 }],
                   { title: 'Dyck path, length ' + w.length + ', height ' + Math.max.apply(null, hs), xlabel: 'letter',
                     ylabel: 'height', height: 240 });
  }

  function cellPlot(a, b, r, s, t, c) {
    var L0 = blog(t) / blog(s), th0 = blog(r) / blog(s);
    var X1 = Math.max(2.0, Math.min(b + 1.5, L0 * 1.6 + 0.5)), Y1 = Math.max(1.5, th0 * 1.6 + 0.5), series = [];
    var cols = ['#C8C8C8', '#9FB8C8', '#C8B39F'];
    for (var h = -a; h <= a; h++) for (var rho = -b; rho <= b; rho++) {
      var pts = [];
      if (h === 0) { if (rho >= 0 && rho <= X1) pts = [[rho, 0], [rho, Y1]]; }
      else {
        [0, X1].forEach(function (L) { var th = (rho - L) / h; if (th >= 0 && th <= Y1) pts.push([L, th]); });
        [0, Y1].forEach(function (th) { var L = rho - h * th; if (L >= 0 && L <= X1) pts.push([L, th]); });
        pts.sort(function (p, q) { return (p[0] - q[0]) || (p[1] - q[1]); });
        pts = pts.length >= 2 ? [pts[0], pts[pts.length - 1]] : [];
      }
      if (pts.length) series.push({ name: '', x: pts.map(function (p) { return p[0]; }), y: pts.map(function (p) { return p[1]; }),
                                    mode: 'line', color: cols[((h % 3) + 3) % 3] });
    }
    series.push({ name: 'the point (Λ, θ) = (log t, log r)/log s of n; c = (' + c.join(', ') + ')', x: [L0], y: [th0],
                  mode: 'points', color: BERMELLON, size: 6 });
    return svgPlot(series, { title: 'The cell of n in the arrangement of the lines Λ + hθ = ρ (|h| ≤ ' + a + ', |ρ| ≤ ' + b + ')',
                             xlabel: 'Λ = log t / log s', ylabel: 'θ = log r / log s', height: 340 });
  }

  // ------------------------------------------------------------------------------------------ 3D figures (lab3d.js)
  /* The 3D figure of each lab is a spec for window.LemmarioFigures['3d'] (labjs/lab3d.js, a copy of Lemmario's
     engine). Floating point here only places things in the drawing; every checked quantity stays exact. */
  var GRAY_PLANE = '#8C8C8C';
  var WORD_COLS = ['#0072B2', '#D55E00', '#009E73', '#CC79A7', '#E69F00', '#56B4E9', '#8C6D31', '#7F7F7F'];
  function hashStr(s) { var h = 0; for (var i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) | 0; return Math.abs(h); }

  /* The plane alpha·x = 1 cut by the box [0, M]^3: its polygon (vertices in cyclic order) or null. */
  function planeInBox(al, M) {
    var C = [], pts = [];
    for (var i = 0; i < 8; i++) C.push([i & 1 ? M : 0, i & 2 ? M : 0, i & 4 ? M : 0]);
    [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(function (e) {
      var P = C[e[0]], Q = C[e[1]], fp = al[0] * P[0] + al[1] * P[1] + al[2] * P[2] - 1, fq = al[0] * Q[0] + al[1] * Q[1] + al[2] * Q[2] - 1;
      if ((fp <= 0 && fq >= 0) || (fp >= 0 && fq <= 0)) {
        if (fp === fq) return;
        var s = fp / (fp - fq);
        pts.push([0, 1, 2].map(function (k) { return P[k] + s * (Q[k] - P[k]); }));
      }
    });
    var uniq = [];
    pts.forEach(function (p) { if (!uniq.some(function (q) { return Math.hypot(p[0] - q[0], p[1] - q[1], p[2] - q[2]) < 1e-9; })) uniq.push(p); });
    if (uniq.length < 3) return null;
    var c = [0, 1, 2].map(function (k) { return uniq.reduce(function (s, p) { return s + p[k]; }, 0) / uniq.length; });
    var nl = Math.hypot(al[0], al[1], al[2]), n = al.map(function (x) { return x / nl; });
    var t = Math.abs(n[0]) < 0.9 ? [1, 0, 0] : [0, 1, 0];
    var e1 = [n[1] * t[2] - n[2] * t[1], n[2] * t[0] - n[0] * t[2], n[0] * t[1] - n[1] * t[0]];
    var l1 = Math.hypot(e1[0], e1[1], e1[2]); e1 = e1.map(function (x) { return x / l1; });
    var e2 = [n[1] * e1[2] - n[2] * e1[1], n[2] * e1[0] - n[0] * e1[2], n[0] * e1[1] - n[1] * e1[0]];
    function dot(u, v) { return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]; }
    uniq.sort(function (p, q) {
      var dp = [p[0] - c[0], p[1] - c[1], p[2] - c[2]], dq = [q[0] - c[0], q[1] - c[1], q[2] - c[2]];
      return Math.atan2(dot(dp, e2), dot(dp, e1)) - Math.atan2(dot(dq, e2), dot(dq, e1));
    });
    return uniq;
  }
  /* A convex polygon as a lab3d surface: two rows walking from v0 along both sides (a strip of quads). */
  function polygonGrid(v) {
    var k = v.length, top = [], bot = [], h = Math.ceil((k - 1) / 2);
    for (var j = 0; j <= h; j++) { top.push(v[Math.min(j, k - 1)]); bot.push(v[(k - j) % k]); }
    return [top, bot];
  }

  /* The 2D companion of a 3D figure (Carles, 25-nov: «3D y al lado 2D»): a small SVG scene with equal scales on
     both axes. shapes: {poly: [[x,y]...], fill, stroke, op} | {line: [[x,y],[x,y]], stroke, dash, width} |
     {pt: [x,y], color, r, star}; legend: [[colour, text], ...]. Floating point, drawing only. */
  function svgScene(title, shapes, o) {
    o = o || {};
    var xs = [], ys = [];
    shapes.forEach(function (s) {
      (s.poly || s.line || [s.pt]).forEach(function (p) { xs.push(p[0]); ys.push(p[1]); });
    });
    if (o.box) { xs.push(o.box[0], o.box[2]); ys.push(o.box[1], o.box[3]); }
    var x0 = Math.min.apply(null, xs), x1 = Math.max.apply(null, xs), y0 = Math.min.apply(null, ys), y1 = Math.max.apply(null, ys);
    // 25-nov: a narrower box (360) for the same panel, so the text (fs = 13) reads at the size of the page's text
    var W = 360, fs = o.fs || 13, L = o.noticks ? 12 : 44, R = 14, T = 14, B = 42, sx = (W - L - R) / ((x1 - x0) || 1);
    var sy = o.free ? sx * (o.free) : sx, H = Math.min(460, Math.round((y1 - y0) * sy + T + B));
    if ((y1 - y0) * sy > H - T - B) sy = (H - T - B) / ((y1 - y0) || 1);
    function X(v) { return (L + (v - x0) * sx).toFixed(1); }
    function Y(v) { return (H - B - (v - y0) * sy).toFixed(1); }
    var LG = svgLegend(o.legend || [], 8, H + 2, W - 16, fs), out = [];
    out.push('<svg viewBox="0 0 ' + W + ' ' + Math.ceil(H + LG.height + 6) + '" class="dk-svg" role="img" aria-label="' + esc(title) + '" xmlns="http://www.w3.org/2000/svg">');
    shapes.forEach(function (s) {
      if (s.poly) out.push('<polygon points="' + s.poly.map(function (p) { return X(p[0]) + ',' + Y(p[1]); }).join(' ') + '" fill="' +
                           (s.fill || 'none') + '" fill-opacity="' + (s.op === undefined ? 1 : s.op) + '" stroke="' + (s.stroke || 'none') + '" stroke-width="0.5"/>');
      else if (s.line) out.push('<line x1="' + X(s.line[0][0]) + '" y1="' + Y(s.line[0][1]) + '" x2="' + X(s.line[1][0]) + '" y2="' + Y(s.line[1][1]) +
                                '" stroke="' + (s.stroke || '#888') + '" stroke-width="' + (s.width || 1) + '"' + (s.dash ? ' stroke-dasharray="4 3"' : '') +
                                (s.op !== undefined ? ' stroke-opacity="' + s.op + '"' : '') + '/>');
      else if (s.star) {
        var cx = Number(X(s.pt[0])), cy = Number(Y(s.pt[1])), r = s.r || 8, d = [];
        for (var i = 0; i < 10; i++) {
          var a = -Math.PI / 2 + i * Math.PI / 5, rr = i % 2 ? r * 0.45 : r;
          d.push((cx + rr * Math.cos(a)).toFixed(1) + ',' + (cy + rr * Math.sin(a)).toFixed(1));
        }
        out.push('<polygon points="' + d.join(' ') + '" fill="' + s.color + '" stroke="#fff" stroke-width="1"/>');
      } else out.push('<circle cx="' + X(s.pt[0]) + '" cy="' + Y(s.pt[1]) + '" r="' + (s.r || 3) + '" fill="' + s.color + '"/>');
    });
    out.push('<text x="' + ((L + W - R) / 2) + '" y="' + (H - 10) + '" text-anchor="middle" font-size="' + fs + '" font-style="italic">' + esc(o.xlabel || '') + '</text>');
    if (o.ylabel) out.push('<text x="14" y="' + ((T + H - B) / 2) + '" font-size="' + fs + '" font-style="italic" text-anchor="middle" transform="rotate(-90 14 ' +
                           ((T + H - B) / 2) + ')">' + esc(o.ylabel) + '</text>');
    if (!o.noticks) {
      out.push('<text x="' + L + '" y="' + (H - B + fs + 2) + '" font-size="' + (fs - 1) + '" text-anchor="start">' + g3(x0) + '</text>');
      out.push('<text x="' + (W - R) + '" y="' + (H - B + fs + 2) + '" font-size="' + (fs - 1) + '" text-anchor="end">' + g3(x1) + '</text>');
      out.push('<text x="' + (L - 4) + '" y="' + (H - B) + '" font-size="' + (fs - 1) + '" text-anchor="end">' + g3(y0) + '</text>');
      out.push('<text x="' + (L - 4) + '" y="' + (T + fs - 2) + '" font-size="' + (fs - 1) + '" text-anchor="end">' + g3(y1) + '</text>');
    }
    out = out.concat(LG.svg);
    out.push('</svg>');
    return '<figure class="dk-fig"><figcaption>' + esc(title) + '</figcaption>' + out.join('') + '</figure>';
  }

  function fig3dThreePrimes(fac, t, n) {
    var lt = blog(t), f = fac.map(function (q) { return q[1]; });
    var x = fac.map(function (q) { return blog(q[0]) / lt; });
    var M = Math.max(1.25, 1.15 * Math.max.apply(null, x));
    var alphas = [], small = [];
    for (var a0 = -f[0]; a0 <= f[0]; a0++) for (var a1 = -f[1]; a1 <= f[1]; a1++) for (var a2 = -f[2]; a2 <= f[2]; a2++) {
      if (a0 <= 0 && a1 <= 0 && a2 <= 0) continue;  // alpha·x = 1 never meets the positive octant
      alphas.push([a0, a1, a2]);
      if (Math.abs(a0) <= 1 && Math.abs(a1) <= 1 && Math.abs(a2) <= 1) small.push([a0, a1, a2]);
    }
    /* 25-nov (Carles: 19 transparent planes on top of each other is too much): by default only the planes that bound
       the cell of n, found by cutting each plane's polygon in the box by the half-spaces of all the others on the side
       of n (a plane bounds the cell iff something of positive area is left: that piece is a face of the cell, drawn
       solid). A slider adds the other planes, faint: those with α ∈ {−1,0,1}³, then all. Drawing only (floating). */
    function side(al) { var v = al[0] * x[0] + al[1] * x[1] + al[2] * x[2] - 1; return v > 0 ? 1 : v < 0 ? -1 : 0; }
    function clip3(poly, al, s) {  // keeps s·(α·y − 1) ≥ 0
      var out = [];
      for (var i = 0; i < poly.length; i++) {
        var P = poly[i], Q = poly[(i + 1) % poly.length];
        var fp = s * (al[0] * P[0] + al[1] * P[1] + al[2] * P[2] - 1), fq = s * (al[0] * Q[0] + al[1] * Q[1] + al[2] * Q[2] - 1);
        if (fp >= 0) out.push(P);
        if ((fp < 0 && fq > 0) || (fp > 0 && fq < 0)) { var r = fp / (fp - fq); out.push([0, 1, 2].map(function (k) { return P[k] + r * (Q[k] - P[k]); })); }
      }
      return out;
    }
    function area3(p) {
      var c = [0, 0, 0];
      for (var i = 0; i < p.length; i++) {
        var u = p[i], v = p[(i + 1) % p.length];
        c[0] += u[1] * v[2] - u[2] * v[1]; c[1] += u[2] * v[0] - u[0] * v[2]; c[2] += u[0] * v[1] - u[1] * v[0];
      }
      return Math.hypot(c[0], c[1], c[2]) / 2;
    }
    var PL = [];  // the planes that meet the box
    alphas.forEach(function (al) {
      var poly = planeInBox(al, M);
      if (poly) PL.push({ al: al, poly: poly, g: al.filter(function (z) { return z !== 0; }).length, s: side(al),
                          small: Math.abs(al[0]) <= 1 && Math.abs(al[1]) <= 1 && Math.abs(al[2]) <= 1 });
    });
    PL.forEach(function (p) {
      var face = p.poly;
      for (var j = 0; j < PL.length && face.length >= 3; j++) if (PL[j] !== p && PL[j].s) face = clip3(face, PL[j].al, PL[j].s);
      p.face = face.length >= 3 && area3(face) > 1e-9 * M * M ? face : null;
    });
    var gc = { 1: '#0072B2', 2: '#009E73', 3: '#6B6B6B' }, gn = { 1: 'one', 2: 'two', 3: 'three' };
    var facets = PL.filter(function (p) { return p.face; }), nSmall = PL.filter(function (p) { return p.small; }).length, ALLCAP = 400;
    var levels = [{ v: 'the cell of n (' + facets.length + ' planes)', keep: function () { return false; } }];
    if (nSmall < PL.length) levels.push({ v: '|α_i| ≤ 1 (' + nSmall + ' planes)', keep: function (p) { return p.small; } });
    if (PL.length <= ALLCAP) levels.push({ v: 'all (' + PL.length + ' planes)', keep: function () { return true; } });
    var cellItems = [];
    [3, 2, 1].forEach(function (g) {
      var fg = facets.filter(function (p) { return p.g === g; });
      fg.forEach(function (p, i) {
        cellItems.push({ type: 'surface', grid: polygonGrid(p.poly), color: gc[g], opacity: 0.13,
                         name: i ? '' : 'planes bounding the cell of n, ' + gn[g] + ' nonzero α_i (' + fg.length + ')' });
      });
    });
    facets.forEach(function (p, i) {
      cellItems.push({ type: 'surface', grid: polygonGrid(p.face), color: gc[p.g], opacity: 0.42,
                       name: i ? '' : 'the faces of the cell of n (solid)' });
    });
    var frames = levels.map(function (lv, k) {
      var its = cellItems.slice();
      if (k) [3, 2, 1].forEach(function (g) {
        var og = PL.filter(function (p) { return !p.face && p.g === g && lv.keep(p); });
        og.forEach(function (p, i) {
          its.unshift({ type: 'surface', grid: polygonGrid(p.poly), color: gc[g], opacity: g === 3 ? 0.035 : 0.05,
                        name: i ? '' : 'other planes, ' + gn[g] + ' nonzero α_i (' + og.length + ', faint)' });
        });
      });
      return its;
    });
    var items = [];
    items.push({ type: 'curve', points: [[x[0], x[1], x[2]], [x[0], x[1], 0]], color: BERMELLON, dash: true, width: 1.5,
                 name: 'drop line of n to x₃ = 0' });
    items.push({ type: 'points', points: [[x[0], x[1], x[2]]], color: BERMELLON, marker: 'star', size: 11,
                 name: 'the point of n: x = (' + x.map(function (z) { return z.toFixed(3); }).join(', ') + ')' });
    items.push({ type: 'points', points: [[0, 0, 0], [M, M, M]], color: '#FFFFFF', size: 0.1, opacity: 0 });  // the box [0, M]^3
    var pat = '(' + f.join(', ') + ')';
    // 2D: the slice by the plane x₁ + x₂ + x₃ = S through the point of n (the paper's slice panel), same colours; it
    // follows the slider: the same planes as the 3D view, and the slice of the cell of n shaded
    var S = x[0] + x[1] + x[2], H3 = Math.sqrt(3) / 2;
    function tri(u, v) { return [u / S + 0.5 * v / S, H3 * v / S]; }  // corners: x₃ at (0,0), x₁ at (1,0), x₂ at the top
    function sliceLine(al) {  // the line α·x = 1 in the slice, in (u, v) = (x₁, x₂), or null
      var A = al[0] - al[2], B = al[1] - al[2], c = 1 - al[2] * S, P = [];
      if (A === 0 && B === 0) return null;
      if (B !== 0) { var v = c / B; if (v >= 0 && v <= S) P.push([0, v]); }
      if (A !== 0) { var u = c / A; if (u >= 0 && u <= S) P.push([u, 0]); }
      if (A !== B) { var u2 = (c - B * S) / (A - B); if (u2 >= 0 && u2 <= S) P.push([u2, S - u2]); }
      var Q2 = [];
      P.forEach(function (p) { if (!Q2.some(function (q) { return Math.abs(p[0] - q[0]) + Math.abs(p[1] - q[1]) < 1e-9; })) Q2.push(p); });
      return Q2.length >= 2 ? [tri(Q2[0][0], Q2[0][1]), tri(Q2[1][0], Q2[1][1])] : null;
    }
    var cellSlice = [[0, 0], [S, 0], [0, S]];  // the cell of n cut by the slice: every plane of the arrangement, on n's side
    alphas.forEach(function (al) {
      var s = side(al), A = al[0] - al[2], B = al[1] - al[2], c = 1 - al[2] * S;
      if (s && cellSlice.length >= 3) cellSlice = clipPoly(cellSlice, -s * A, -s * B, -s * c);
    });
    var LIGHT = '#F2C4A3';
    function flat(k) {
      var lv = levels[k], sh = [{ poly: [tri(0, 0), tri(S, 0), tri(0, S)], fill: '#ffffff', stroke: '#555555' }];
      if (cellSlice.length >= 3) sh.push({ poly: cellSlice.map(function (p) { return tri(p[0], p[1]); }), fill: LIGHT, op: 0.8, stroke: 'none' });
      var nOther = 0;
      [3, 2, 1].forEach(function (g) {
        PL.forEach(function (p) {
          if (p.g !== g || p.face || !k || !lv.keep(p)) return;
          var ln = sliceLine(p.al);
          if (ln) { sh.push({ line: ln, stroke: gc[g], width: 0.8, op: 0.45 }); nOther++; }
        });
      });
      var gseen = {};
      facets.forEach(function (p) {
        var ln = sliceLine(p.al);
        if (ln) { sh.push({ line: ln, stroke: gc[p.g], width: 2.4 }); gseen[p.g] = 1; }
      });
      sh.push({ pt: tri(x[0], x[1]), color: BERMELLON, star: true, r: 9 });
      var leg = [[LIGHT, 'the cell of n in this slice'], [BERMELLON, 'the point of n']];
      [1, 2, 3].forEach(function (g) { if (gseen[g]) leg.push([gc[g], 'bounding plane, ' + gn[g] + ' nonzero α_i (thick)']); });
      if (nOther) leg.push(['#BBBBBB', 'other planes (thin, faint)']);
      return svgScene('The slice x₁ + x₂ + x₃ = ' + S.toFixed(3) + ' through the point of n: each plane is a line; shown: ' + lv.v, sh,
                      { noticks: true, xlabel: 'corners: x₃ (left), x₁ (right), x₂ (top)', legend: leg });
    }
    return { kind: '3d', axes: ['x₁', 'x₂', 'x₃'], items: items, zoomOut: 2, flat: flat,
             slider: { label: 'planes shown', values: levels.map(function (lv) { return lv.v; }), items: frames, start: 0 },
             title: 'n = ' + n + ', three odd primes ' + fac.map(function (q) { return q[0]; }).join(', ') + ' (pattern ' + pat +
                    '), x_i = log p_i / log t: the arrangement of the planes α·x = 1 (|α_i| ≤ f_i, ' + alphas.length + ' planes, ' + PL.length +
                    ' meet the box [0, ' + M.toFixed(2) + ']³); the word is constant on each cell. Shown: the ' + facets.length +
                    ' planes that bound the cell of n and its faces; the slider adds the others, faint' +
                    (PL.length > ALLCAP ? ' (those with α ∈ {−1,0,1}³; all ' + PL.length + ' would hide the figure)' : '') };
  }

  function fig3dTwoPrimes(T, t, n) {
    var a = T.a, b = T.b, r = BigInt(T.r), s = BigInt(T.s), ls = blog(s);
    var L0 = blog(t) / ls, th0 = blog(r) / ls;
    var X1 = Math.max(2.0, Math.min(b + 1.5, L0 * 1.6 + 0.5)), Y1 = Math.max(1.5, th0 * 1.6 + 0.5);
    function wordAt(L, th) {  // drawing only: the clipped vector in floating point, then Z(c) and the word
      var c = [];
      for (var h = -a; h <= a; h++) c.push(N.clip(Math.floor(L + h * th), b));
      return N.wordFromCounts(N.Z(a, b, c));
    }
    // flat tiles, each at the height of the word at its centre: terraces without the slanted walls a single surface
    // would draw between grid points of different cells
    var hmax = 1, G = 44, dx = X1 / G, dy = Y1 / G, tiles = [];
    for (var i = 0; i < G; i++) for (var j = 0; j < G; j++) {
      var w = wordAt(dx * (i + 0.5013), dy * (j + 0.4987)), hgt = Math.max.apply(null, N.heights(w));
      hmax = Math.max(hmax, hgt);
      tiles.push([i, j, hgt, WORD_COLS[hashStr(w) % WORD_COLS.length]]);
    }
    var zs = 0.35 * Math.max(X1, Y1) / hmax;  // the height is drawn at this scale
    var items = tiles.map(function (tl, k) {
      var x0 = tl[0] * dx, y0 = tl[1] * dy, z = tl[2] * zs;
      return { type: 'surface', grid: [[[x0, y0, z], [x0, y0 + dy, z]], [[x0 + dx, y0, z], [x0 + dx, y0 + dy, z]]], color: tl[3], opacity: 0.6,
               name: k ? '' : 'terrace: height of the Dyck word of the cell at (Λ, θ) (colour: the word; sampled for drawing)' };
    });
    var named = false, flatLines = [];
    for (var h = -a; h <= a; h++) for (var rho = -b; rho <= b; rho++) {
      var pts = [];
      if (h === 0) { if (rho >= 0 && rho <= X1) pts = [[rho, 0], [rho, Y1]]; }
      else {
        [0, X1].forEach(function (L) { var th = (rho - L) / h; if (th >= 0 && th <= Y1) pts.push([L, th]); });
        [0, Y1].forEach(function (th) { var L = rho - h * th; if (L >= 0 && L <= X1) pts.push([L, th]); });
        pts.sort(function (p, q) { return (p[0] - q[0]) || (p[1] - q[1]); });
        pts = pts.length >= 2 ? [pts[0], pts[pts.length - 1]] : [];
      }
      if (pts.length) flatLines.push({ line: pts, stroke: '#4A5A69', width: 0.8 });
      if (pts.length) items.push({ type: 'curve', points: pts.map(function (p) { return [p[0], p[1], 0]; }), color: '#7A8A99', width: 1,
                                   name: named ? '' : 'lines Λ + hθ = ρ at height 0 (|h| ≤ ' + a + ', |ρ| ≤ ' + b + ')' });
      if (pts.length) named = true;
    }
    var hn = Math.max.apply(null, N.heights(N.wordFromCounts(N.Z(a, b, T.c))));  // the exact word of n's cell
    items.push({ type: 'curve', points: [[L0, th0, 0], [L0, th0, hn * zs]], color: BERMELLON, dash: true, width: 1.5,
                 name: 'drop line of n' });
    items.push({ type: 'points', points: [[L0, th0, hn * zs]], color: BERMELLON, marker: 'star', size: 11,
                 name: 'n: (Λ, θ) = (' + L0.toFixed(3) + ', ' + th0.toFixed(3) + '), its word has height ' + hn });
    // a sweep of θ along the vertical line Λ = Λ(n): the marker crosses the lines Λ + hθ = ρ and the word changes
    // (slider; the word at each step is read in floating point, for drawing only)
    var sweep = [], vals = [], NS = 30;
    for (var st = 0; st <= NS; st++) {
      var thS = Y1 * (st + 0.0137) / (NS + 0.03), wS = wordAt(L0, thS), hS = Math.max.apply(null, N.heights(wS));
      vals.push(thS.toFixed(2));
      sweep.push([{ type: 'points', points: [[L0, thS, hS * zs]], color: '#000000', marker: 'dot', size: 6,
                    name: 'θ sweep: word ' + (wS.length <= 60 ? wS : wS.slice(0, 60) + '…') + ' (height ' + hS + ')' },
                  { type: 'curve', points: [[L0, 0, 0], [L0, Y1, 0]], color: '#000000', dash: true, width: 1, name: 'the line Λ = Λ(n) swept' }]);
    }
    var nearest = 0;
    vals.forEach(function (x, i) { if (Math.abs(Number(x) - th0) < Math.abs(Number(vals[nearest]) - th0)) nearest = i; });
    // 2D: the same tiles seen from above (colour = word), the lines and the point of n: the plane of the paper's figures
    var flat2d = svgScene('Seen from above: the cells of (Λ, θ), coloured by word, and the point of n',
      tiles.map(function (tl) {
        var x0 = tl[0] * dx, y0 = tl[1] * dy;
        return { poly: [[x0, y0], [x0 + dx, y0], [x0 + dx, y0 + dy], [x0, y0 + dy]], fill: tl[3], op: 0.6 };
      }).concat(flatLines, [{ line: [[L0, 0], [L0, Y1]], stroke: '#000000', dash: true, width: 1 },
                            { pt: [L0, th0], color: BERMELLON, star: true, r: 9 }]),
      { xlabel: 'Λ = log t / log s', ylabel: 'θ = log r / log s',
        legend: [['#4A5A69', 'lines Λ + hθ = ρ'], [BERMELLON, 'n'], ['#000000', 'line of the θ sweep']] });
    return { kind: '3d', axes: ['Λ', 'θ', 'height'], items: items, zoomOut: 1, flat: flat2d,
             slider: { label: 'θ', values: vals, items: sweep, start: nearest },
             title: 'n = ' + n + ', two odd primes (r = ' + T.r + ', s = ' + T.s + '), Λ = log t / log s, θ = log r / log s: ' +
                    'each cell of the lines Λ + hθ = ρ is a terrace ' +
                    'at the height of its word (max height ' + hmax + ')' };
  }

  function fig3dOnePrime(p, e, Nn, n) {
    var q = e + 1, items = [], ys = 2 * q / Math.max(1, e) * 0.6;
    for (var Nj = 0; Nj <= e; Nj++) {
      var oc = [];
      for (var j = 1; j <= q; j++) oc.push(Math.min(q, Nj + j));
      var hs = N.heights(N.wordFromCounts(oc)), mine = Nj === Nn;
      items.push({ type: 'curve', points: hs.map(function (hh, i) { return [i, Nj * ys, hh]; }), color: mine ? BERMELLON : '#5B8DB8',
                   width: mine ? 3.2 : 1.4, name: mine ? 'the word of n: O_' + q + '(' + Nn + ')' : (Nj === (Nn === 0 ? 1 : 0) ? 'the other words O_' + q + '(N) of one prime' : '') });
    }
    items.push({ type: 'points', points: [[0, Nn * ys, 0]], color: BERMELLON, marker: 'star', size: 10,
                 name: 'N = min(⌊log t / log p⌋, ' + e + ') = ' + Nn });
    var ser = [];
    for (var N2 = 0; N2 <= e; N2++) {
      var oc2 = [];
      for (var j2 = 1; j2 <= q; j2++) oc2.push(Math.min(q, N2 + j2));
      var hs2 = N.heights(N.wordFromCounts(oc2));
      ser.push({ name: N2 === Nn ? 'the word of n: O_' + q + '(' + Nn + ')' : (N2 === (Nn === 0 ? 1 : 0) ? 'the other words O_' + q + '(N)' : ''),
                 x: hs2.map(function (_, i) { return i; }), y: hs2, mode: 'line', color: N2 === Nn ? BERMELLON : '#5B8DB8' });
    }
    ser.push(ser.splice(Nn, 1)[0]);  // the word of n on top
    var flat2d = svgPlot(ser, { title: 'Seen from the side: the ' + q + ' Dyck paths on top of each other', xlabel: 'letter', ylabel: 'height', width: 380, height: 260 });
    return { kind: '3d', axes: ['letter', 'N', 'height'], items: items, zoomOut: 1, flat: flat2d,
             title: 'n = ' + n + ', one odd prime p = ' + p + ', m = p^' + e + ': the ' + q + ' words O_' + q + '(N), N = 0 … ' + e +
                    ', as Dyck paths side by side; n picks N = ' + Nn };
  }

  function fig3dLetters(n, m, t, w) {  // any n: each letter at its place log v / log t, its type, the height after it
    var Dm = N.divisors(m), lt = blog(t), letters = [];
    Dm.forEach(function (d) { letters.push([d, 0]); letters.push([t * d, 1]); });
    letters.sort(function (u, v) { return N.bcmp(u[0], v[0]); });  // exact order: the order of the word
    var hs = N.heights(w), xmax = blog(letters[letters.length - 1][0]) / lt || 1, hmax = Math.max.apply(null, hs) || 1;
    var zs = 0.45 * xmax / hmax, yo = 0.35 * xmax, op = [], cl = [], path = [];
    letters.forEach(function (u, i) {
      var p = [blog(u[0]) / lt, u[1] * yo, hs[i + 1] * zs];
      (u[1] ? cl : op).push(p);
      path.push(p);
    });
    var flat2d = svgPlot([{ name: 'the Dyck path against the place log v / log t of each letter', x: path.map(function (p) { return p[0]; }),
                            y: hs.slice(1), mode: 'line', color: '#7A8A99' },
                          { name: '“(”', x: op.map(function (p) { return p[0]; }), y: op.map(function (p) { return p[2] / zs; }), mode: 'points', color: AZUL, size: 3 },
                          { name: '“)”', x: cl.map(function (p) { return p[0]; }), y: cl.map(function (p) { return p[2] / zs; }), mode: 'points', color: NARANJA, size: 3 }],
                         { title: 'Seen from the front: height against log v / log t', xlabel: 'log v / log t', ylabel: 'height', width: 380, height: 260 });
    return { kind: '3d', axes: ['log v / log t', 'type', 'height'], zoomOut: 1, flat: flat2d,
             items: [{ type: 'curve', points: path, color: '#7A8A99', width: 1.2, name: 'the word, letter after letter' },
                     { type: 'points', points: op, color: AZUL, size: 4, name: '“(”: a divisor d of m' },
                     { type: 'points', points: cl, color: NARANJA, size: 4, name: '“)”: a partner t·d' }],
             title: 'n = ' + n + ': the letters of the word at their places log v / log t (v = d or t·d), “(” in front and “)” behind, ' +
                    'lifted to the height of the Dyck path after each letter' };
  }

  function mount3d(box, specs) {  // specs: one spec or a list, each into its slot <div class="dk-3d" data-k="i">
    [].concat(specs || []).forEach(function (spec, k) {
      var el = box.querySelector('.dk-3d[data-k="' + k + '"]');
      if (!el || !spec) return;
      var kind = (window.LemmarioFigures || {})['3d'];
      if (!kind) { el.textContent = 'The 3D figure needs labjs/lab3d.js, which did not load.'; return; }
      kind.mount(el, spec);
      // lab3d.js scales the data box to the canvas; a box with three similar spans overflows it at the initial
      // view, so start a little further away with the figure's own «zoom out» button (⟲ returns to its default)
      var zout = el.querySelector('.l3-zout');
      for (var i = 0; zout && i < (spec.zoomOut || 0); i++) zout.click();
      // or closer, with its «zoom in» (a figure that is wide and flat, e.g. Figure 5 in 3D, fills the canvas that way)
      var zin = el.querySelector('.l3-zin');
      for (var j = 0; zin && j < (spec.zoomIn || 0); j++) zin.click();
      // the 2D companion at its side: a fixed SVG, or a function of the slider's frame that follows it (the input of
      // the range, and the ▶ run, both rewrite the value label .l3-val)
      var el2 = box.querySelector('.dk-2d[data-k="' + k + '"]');
      if (!el2 || !spec.flat) return;
      if (typeof spec.flat !== 'function') { el2.innerHTML = spec.flat; return; }
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
  function slots3d(specs) {
    return [].concat(specs || []).map(function (_, k) {
      return '<div class="dk-pair" data-k="' + k + '"><div class="dk-3d" data-k="' + k + '"></div><div class="dk-2d" data-k="' + k + '"></div></div>';
    }).join('');
  }

  // ------------------------------------------------------------ Figure 5 in 3D: the three coincidence mechanisms
  /* The pairs of fig_mecanismos.py (paper): two cells (Λ, θ) with the same word, exactly (rationals). */
  var MECH = [
    { name: 'empty graph: the fibre of O(0)', a: 1, b: 3, pts: [[[1, 20], [1, 2]], [[1, 20], [5, 2]]],
      why: 'Λ → 0: every “)” follows its own “(”; the cell only records where θ sits among the fractions j/h, every such interval gives a different vector and the same word ()^k.' },
    // 25-nov: the pair of the paper's corrected figure (the former (9/5, 2/5), (7/2, 36/5) was the case d = 0, a
    // class O, not Q): I₁ with β = 2, d = 1, and its partner J(7, 1) in Lemma Q
    { name: 'exchange of progressions (family Q, a = 1)', a: 1, b: 6, pts: [[[71, 20], [61, 40]], [[501, 100], [41, 10]]],
      why: 'second row shifted by θ ≈ 1.5 (cell 1) or θ ≈ 4.1 (cell 2). A progression of closing ranks moves from one row to the other; the multiset of ranks, and hence the word, does not change.' },
    { name: 'reflection of a component (family A, a = 2)', a: 2, b: 3, pts: [[[3, 20], [9, 10]], [[3, 20], [11, 10]]],
      why: 'θ just below or just above an integer: inside each integer level the rows appear in reversed order, so the unit interval graph is reflected and the word is the same.' }
  ];
  var ROWCOL = ['#0072B2', '#009E73', '#CC79A7'];  // FILAS of fig_mecanismos.py
  function qf(x) { return Number(x.n) / Number(x.d); }
  /* The word of the configuration (Λ, θ): openings iθ + j, closings Λ + iθ + j, merged exactly (a tie between an
     opening and a closing is an error, as in the paper's script). */
  function mechWord(a, b, L, th) {
    var ev = [];
    for (var i = 0; i <= a; i++) for (var j = 0; j <= b; j++) {
      var o = N.qadd(N.qmulInt(th, i), N.Q(j));
      ev.push([o, 0]); ev.push([N.qadd(L, o), 1]);
    }
    ev.sort(function (u, v) { return N.qcmp(u[0], v[0]) || (u[1] - v[1]); });
    for (var k = 0; k + 1 < ev.length; k++)
      if (N.qcmp(ev[k][0], ev[k + 1][0]) === 0 && ev[k][1] !== ev[k + 1][1]) throw new Error('tie between an opening and a closing');
    return ev.map(function (e) { return e[1] ? ')' : '('; }).join('');
  }
  function mechVec(a, b, L, th) {
    var c = [];
    for (var h = -a; h <= a; h++) c.push(N.clip(N.qfloor(N.qadd(L, N.qmulInt(th, h))), b));
    return c;
  }
  function mechData() {
    return MECH.map(function (m) {
      var cf = m.pts.map(function (p) {
        var L = N.Q(p[0][0], p[0][1]), th = N.Q(p[1][0], p[1][1]);
        return { L: L, th: th, word: mechWord(m.a, m.b, L, th), c: mechVec(m.a, m.b, L, th),
                 viaZ: N.wordFromCounts(N.Z(m.a, m.b, mechVec(m.a, m.b, L, th))) };
      });
      return { m: m, cf: cf, same: cf[0].word === cf[1].word, distinct: cf[0].c.join() !== cf[1].c.join(),
               zok: cf[0].viaZ === cf[0].word && cf[1].viaZ === cf[1].word };
    });
  }
  function fig3dMechanisms(data, start) {
    /* 25-nov (Carles: the two layers came out small and squashed): as in the 2D panel, cell 1 on top, cell 2 under it
       and the common word at the bottom, spread over a height of about 0.6 of the length, so the figure fills the canvas;
       the height of the Dyck path is scaled per mechanism to its band. */
    var ZS = [5.6, 3.3], WORDBAND = 1.9, BAR = 0.45, frames = [];
    data.forEach(function (D) {
      var m = D.m, a = m.a, b = m.b, items = [];
      var xmax = Math.max.apply(null, D.cf.map(function (c) { return qf(c.L) + a * qf(c.th) + b; }));
      var sx = 10 / xmax, ys = 1.4;
      D.cf.forEach(function (c, k) {
        var z = ZS[k], L = qf(c.L), th = qf(c.th);
        for (var i = 0; i <= a; i++) {
          items.push({ type: 'curve', points: [[0, i * ys, z], [10.4, i * ys, z]], color: '#C8C8C8', width: 1,
                       name: i === 0 ? 'cell ' + (k + 1) + (k ? ' (middle)' : ' (top)') + ': Λ = ' + L.toFixed(2) + ', θ = ' + th.toFixed(2) +
                                       ', c = (' + c.c.join(', ') + ')' : '' });
          var op = [];
          for (var j = 0; j <= b; j++) {
            op.push([(i * th + j) * sx, i * ys, z]);
            var xc = (L + i * th + j) * sx;
            items.push({ type: 'curve', points: [[xc, i * ys, z - BAR], [xc, i * ys, z + BAR]], color: ROWCOL[i], width: 2.4,
                         name: k === 0 && j === 0 ? 'row i = ' + i + ': closings Λ + ' + i + 'θ + j (bars)' : '' });
          }
          items.push({ type: 'points', points: op, color: ROWCOL[i], size: 5,
                       name: k === 0 ? 'row i = ' + i + ': openings ' + i + 'θ + j (dots)' : '' });
        }
      });
      var hs = N.heights(D.cf[0].word), dx = 10 / (hs.length - 1), hz = WORDBAND / Math.max(1, Math.max.apply(null, hs));
      items.push({ type: 'curve', points: hs.map(function (h, t) { return [t * dx, 0, h * hz]; }), color: '#222222', width: 2.2,
                   name: 'the common word ' + D.cf[0].word + ' as a Dyck path (bottom)' });
      frames.push(items);
    });
    // 2D: the paper's row of Figure 5 for the mechanism of the slider (true positions, units of log s)
    function flat(k) {
      var D = data[k], a = D.m.a, b = D.m.b, sh = [];
      var xmax = Math.max.apply(null, D.cf.map(function (c) { return qf(c.L) + a * qf(c.th) + b; })), u = xmax / 10;
      D.cf.forEach(function (c, kk) {
        var y = (1 - kk) * 3.2 * u, L = qf(c.L), th = qf(c.th);
        sh.push({ line: [[0, y], [xmax, y]], stroke: '#cccccc' });
        for (var i = 0; i <= a; i++) for (var j = 0; j <= b; j++) {
          var yo = y - i * 0.35 * u;
          sh.push({ line: [[L + i * th + j, yo - 0.3 * u], [L + i * th + j, yo + 0.3 * u]], stroke: ROWCOL[i], width: 2 });
          sh.push({ pt: [i * th + j, yo], color: ROWCOL[i], r: 3.5 });
        }
      });
      // the word in its own band under cell 2 (its height scaled per mechanism, so a tall word never reaches the cells)
      var hs = N.heights(D.cf[0].word), dxp = xmax / (hs.length - 1), hb = 2.6 * u / Math.max(1, Math.max.apply(null, hs));
      var yb = -(1.2 + a * 0.35) * u - 2.6 * u;
      for (var s2 = 0; s2 + 1 < hs.length; s2++)
        sh.push({ line: [[s2 * dxp, yb + hs[s2] * hb], [(s2 + 1) * dxp, yb + hs[s2 + 1] * hb]], stroke: '#222222', width: 1.4 });
      return svgScene('Figure 5 of the paper, mechanism ' + (k + 1) + ': cell 1 (top) and cell 2, and the common word (below)', sh,
                      { noticks: true, xlabel: 'position (units of log s)',
                        legend: ROWCOL.slice(0, a + 1).map(function (c, i) { return [c, 'row i = ' + i + ': dots ' + i + 'θ + j, bars Λ + ' + i + 'θ + j']; })
                                .concat([['#222222', 'the common word as a Dyck path']]) });
    }
    return { kind: '3d', axes: ['position (scaled)', 'row i', 'layer'], items: [], zoomOut: 0, flat: flat,
             slider: { label: 'mechanism', values: data.map(function (D, k) { return (k + 1) + ': ' + D.m.name; }), items: frames,
                       start: start },
             title: 'Figure 5 in 3D: two different cells (Λ, θ), one above the other, with the same word. Each row i is a layer in ' +
                    'depth; dots are openings iθ + j, bars closings Λ + iθ + j (positions in units of log s, scaled per mechanism)' };
  }

  function runMech(v) {
    var k = Number(v.mech);
    if (!(k >= 0 && k <= 2)) return { error: 'Choose a mechanism 1, 2 or 3.' };
    var data = mechData(), bad = false, rows = [];
    var txt = 'Three ways two different cells give the same word (the paper’s Figure 5), recomputed exactly with rationals. ';
    data.forEach(function (D, i) {
      var ok = D.same && D.distinct && D.zok;
      bad = bad || !ok;
      txt += (i + 1) + '. ' + D.m.name + ' (a = ' + D.m.a + ', b = ' + D.m.b + '): ' + D.m.why + ' Check: same word ' +
        (D.same ? 'yes' : 'NO') + ', different cell vectors ' + (D.distinct ? 'yes' : 'NO') + ', and each word equals the one of Z(c) ' +
        (D.zok ? 'yes' : 'NO') + '. ';
      D.cf.forEach(function (c, j) {
        rows.push([(i + 1) + '.' + (j + 1), D.m.a + ', ' + D.m.b, N.qstr(c.L), N.qstr(c.th), '(' + c.c.join(', ') + ')', c.word]);
      });
    });
    var head = ['pair.cell', 'a, b', 'Λ', 'θ', 'cell vector c', 'word'];
    var plots = data.map(function (D, i) {
      var hs = N.heights(D.cf[0].word), idx = hs.map(function (_, t) { return t; });
      return svgPlot([{ name: 'the common word of the pair, as a Dyck path', x: idx, y: hs, mode: 'line', color: '#222222' }],
                     { title: 'Mechanism ' + (i + 1) + ': ' + D.m.name, xlabel: 'letter', ylabel: 'height', height: 200 });
    });
    return { text: txt, plots: plots, fig3d: fig3dMechanisms(data, k), table: table(head, rows), csv: { head: head, rows: rows }, bad: bad };
  }
  function randomMech() { return { mech: String(randInt(0, 2)) }; }

  // --------------------------------------------- Figure 6 in 3D: the classes of cells for a = 1 in (Λ, Λ − θ)
  function clipPoly(poly, A, B, C) {  // Sutherland–Hodgman, keeps A·X + B·Y ≤ C (drawing only, floating point)
    var out = [];
    for (var i = 0; i < poly.length; i++) {
      var P = poly[i], Qp = poly[(i + 1) % poly.length], fp = A * P[0] + B * P[1] - C, fq = A * Qp[0] + B * Qp[1] - C;
      if (fp <= 0) out.push(P);
      if ((fp < 0 && 0 < fq) || (fq < 0 && 0 < fp)) { var s = fp / (fp - fq); out.push([P[0] + s * (Qp[0] - P[0]), P[1] + s * (Qp[1] - P[1])]); }
    }
    return out;
  }
  function polyArea(p) {
    var s = 0;
    for (var i = 0; i < p.length; i++) { var q = p[(i + 1) % p.length]; s += p[i][0] * q[1] - q[0] * p[i][1]; }
    return Math.abs(s) / 2;
  }
  /* One b: the exact classes (cells of N.cells(1, b) grouped by word, labelled O(s) or Q(τ,d) as in
     fig_rejilla_a1.py) and the polygons of the window of the paper's figure, each with its triple. */
  function classesA1(b) {
    var Tn = 2 * b + 2, vecs = N.cells(1, b), byWord = {}, wordOf = {};
    vecs.forEach(function (c) {
      var w = N.wordFromCounts(N.Z(1, b, c));
      wordOf[c.join(',')] = w; (byWord[w] = byWord[w] || []).push(c);
    });
    var O = {};
    for (var s = 0; s < Tn; s++) {
      var cs = [];
      for (var x = s + 1; x < Tn; x++) cs.push(x);
      for (x = 0; x <= s; x++) cs.push(Tn);
      O[N.wordFromCounts(cs)] = s;
    }
    var label = {}, nO = 0, nQ = 0, nOther = 0;
    Object.keys(byWord).forEach(function (w) {
      if (byWord[w].length < 2) return;
      if (O[w] !== undefined) { label[w] = { t: 'O', s: 'O(' + O[w] + ')' }; nO++; return; }
      var Z = N.Z(1, b, byWord[w][0]), tau = Z[0], ell = Tn - tau, prof = [], d = 0;
      for (var q = 0; q < ell; q++) { var cnt = Z.filter(function (z) { return z === tau + q; }).length; prof.push(cnt); if (!cnt) d++; }
      var form = [];
      for (q = 0; q < d; q++) form.push(1, 0);
      for (q = 0; q < ell - 3 * d; q++) form.push(1);
      for (q = 0; q < d; q++) form.push(2);
      if (d >= 1 && prof.join() === form.join()) { label[w] = { t: 'Q', s: 'Q(' + tau + ',' + d + ')' }; nQ++; }
      else { label[w] = { t: 'X', s: 'other' }; nOther++; }
    });
    // the polygons of the window Λ ∈ (0, (2b+3)/2], Λ − θ ∈ [−b−2, b+1], θ > 0, cut by Λ ∈ Z, Λ−θ ∈ Z, Λ+θ ∈ Z
    var Amax = (2 * b + 3) / 2, Bmin = -b - 2, Bmax = b + 1, polys = [], seen = {};
    function cl(v) { return Math.max(-b - 1, Math.min(b, Math.floor(v))); }
    for (var mA = 0; mA <= Math.floor(Amax); mA++) for (var nB = Bmin; nB <= Bmax; nB++) {
      var x0 = mA, x1 = Math.min(mA + 1, Amax), y0 = Math.max(nB, Bmin), y1 = Math.min(nB + 1, Bmax);
      if (x0 >= x1 || y0 >= y1) continue;
      var sq = clipPoly([[x0, y0], [x1, y0], [x1, y1], [x0, y1]], -1, 1, 0);
      if (sq.length < 3) continue;
      for (var k = 2 * mA - nB - 2; k <= 2 * mA - nB + 2; k++) {
        var p = clipPoly(clipPoly(sq, -2, 1, -k), 2, -1, k + 1);
        if (p.length < 3 || polyArea(p) < 1e-12) continue;
        var cx = 0, cy = 0;
        p.forEach(function (v) { cx += v[0] / p.length; cy += v[1] / p.length; });
        var key = [cl(cy), cl(cx), cl(2 * cx - cy)].join(',');  // c = (c_−1, c_0, c_1) = (Λ−θ, Λ, Λ+θ) clipped
        seen[key] = 1;
        polys.push({ p: p, key: key });
      }
    }
    var exactKeys = Object.keys(wordOf).sort().join(';'), polyKeys = Object.keys(seen).sort().join(';');
    return { b: b, R: vecs.length, W: Object.keys(byWord).length, byWord: byWord, wordOf: wordOf, label: label,
             nO: nO, nQ: nQ, nOther: nOther, polys: polys, same: exactKeys === polyKeys, WA: b >= 2 ? N.WA(b) : null };
  }
  var CLS_COL = { O: ['#cfe3f2', '#7fb3dc'], Q: ['#f6c9a8', '#e8894a'], X: ['#d4b3e0', '#a66bbf'], single: '#dedede' };
  function fig3dClassesA1(start) {
    var bs = [2, 3, 4, 5, 6, 7, 8], frames = [], maxSize = 1, all = bs.map(classesA1), info = [];
    all.forEach(function (C) { Object.keys(C.byWord).forEach(function (w) { maxSize = Math.max(maxSize, C.byWord[w].length); }); });
    all.forEach(function (C) {
      var sc = 1 / (C.b + 1), hz = 1.1 / maxSize, items = [], tone = {}, iO = 0, iQ = 0, iX = 0, namedT = {};
      Object.keys(C.label).sort().forEach(function (w) {
        var t = C.label[w].t; tone[w] = CLS_COL[t][(t === 'O' ? iO++ : t === 'Q' ? iQ++ : iX++) % 2];
      });
      C.polys.forEach(function (P) {
        var w = C.wordOf[P.key], size = w ? C.byWord[w].length : 0, lab = w && C.label[w], col = lab ? tone[w] : CLS_COL.single;
        var z = size * hz, pts = P.p.map(function (v) { return [v[0] * sc, v[1] * sc, z]; });
        var t = lab ? lab.t : 'single';
        var nm = { O: 'class O(s): the word of one prime, shared by ≥ 2 cells', Q: 'class Q(τ,d)', X: 'other class of size ≥ 2 (not O or Q)',
                   single: 'word of a single cell (height 1)' }[t];
        items.push({ type: 'surface', grid: polygonGrid(pts), color: col, opacity: lab ? 0.85 : 0.5, name: namedT[t] ? '' : nm });
        namedT[t] = 1;
        if (lab) for (var i = 0; i < pts.length; i++) {
          var u = pts[i], v = pts[(i + 1) % pts.length];
          items.push({ type: 'surface', grid: [[[u[0], u[1], 0], [v[0], v[1], 0]], [u, v]], color: col, opacity: 0.35 });
        }
      });
      // the line Λ − θ = Λ (θ = 0), the edge of the window
      items.push({ type: 'curve', points: [[0, 0, 0], [C.b + 1, C.b + 1, 0].map(function (x, i) { return i < 2 ? x * sc : 0; })], color: '#222222', width: 1.6,
                   name: 'θ = 0 (edge of the window)' });
      items.push({ type: 'points', points: [], color: '#ffffff',
                   name: 'b = ' + C.b + ': ' + C.R + ' cells, ' + C.W + ' words (Theorem A: ' + C.WA + (C.WA === C.W ? ', agrees' : ', DIFFERS') +
                         '), ' + C.nO + ' classes O, ' + C.nQ + ' classes Q' + (C.nOther ? ', ' + C.nOther + ' OTHER' : '') +
                         '; polygons = exact cells: ' + (C.same ? 'yes' : 'NO') });
      frames.push(items);
      info.push(C);
    });
    var k0 = Math.max(0, bs.indexOf(start));
    // 2D: the paper's Figure 6 for the b of the slider, same colours (it follows the slider)
    function flat(k) {
      var C = info[k], tone = {}, iO = 0, iQ = 0, iX = 0;
      Object.keys(C.label).sort().forEach(function (w) {
        var t = C.label[w].t; tone[w] = CLS_COL[t][(t === 'O' ? iO++ : t === 'Q' ? iQ++ : iX++) % 2];
      });
      var shapes = C.polys.map(function (P) {
        var w = C.wordOf[P.key];
        return { poly: P.p, fill: w && C.label[w] ? tone[w] : CLS_COL.single, stroke: '#9a9a9a' };
      });
      shapes.push({ line: [[0, 0], [C.b + 1, C.b + 1]], stroke: '#222222', width: 1.4 });
      return svgScene('Figure 6 of the paper, b = ' + C.b + ': ' + C.R + ' cells, ' + C.W + ' words, ' + C.nO + ' classes O and ' + C.nQ + ' classes Q',
                      shapes, { xlabel: 'Λ = log t / log s', ylabel: 'Λ − θ',
                                legend: [[CLS_COL.O[1], 'class O(s)'], [CLS_COL.Q[1], 'class Q(τ,d)'], [CLS_COL.single, 'word of a single cell'], ['#222222', 'θ = 0']] });
    }
    return { spec: { kind: '3d', axes: ['Λ', 'Λ − θ', 'class size'], items: [], zoomOut: 1, flat: flat,
                     slider: { label: 'b', values: bs, items: frames, start: k0 },
                     colorbar: { label: 'class', stops: [['O(s)', CLS_COL.O[1]], ['Q(τ,d)', CLS_COL.Q[1]], ['single cell', CLS_COL.single]] },
                     title: 'Figure 6 in 3D: the cells for a = 1 in the plane (Λ, Λ − θ) (window of the paper, scaled by 1/(b+1)); ' +
                            'each cell is raised to the size of its class (how many cells share its word), coloured by the kind of class' },
             info: info };
  }

  function runWord(v) {
    var raw = String(v.n == null ? '13720' : v.n).replace(/[ _]/g, '');
    if (!/^\d+$/.test(raw)) return { error: 'n must be a positive integer.' };
    var n = BigInt(raw);
    if (n < 1n || n > 1000000000000n) return { error: 'Choose 1 ≤ n ≤ 10^12.' };
    var D = N.wordData(n), w = D.word, m = BigInt(D.m), t = BigInt(D.t), fac = N.factor(m), k = D.k;
    var pattern = fac.map(function (x) { return x[1]; }).sort(function (x, y) { return y - x; });
    var facStr = (m > 1n && !(fac.length === 1 && fac[0][1] === 1)) ?
      ' = ' + fac.map(function (x) { return x[1] > 1 ? x[0] + '^' + x[1] : String(x[0]); }).join(' · ') : '';
    var txt = 'n = ' + n + ' = 2^' + D.e1 + ' · ' + m + ', so t = 2^e = ' + t + ' and the odd part is m = ' + m + facStr +
      '. Semilength k = τ(m) = ' + k + ' (Lemma 2.1); pattern of m: (' + (pattern.join(', ') || '—') + '). The word read from the ' +
      'definition (D_n △ 2D_n) is ' + (w.length <= 120 ? w : w.slice(0, 120) + '…') + '. ';
    txt += 'Rebuilt from the counts C(n) of (1) it is ' + (D.ok_C ? 'the same' : 'DIFFERENT (error)') + '; Dyck: ' + (D.dyck ? 'yes' : 'NO') +
      '; symmetric (Caballero, Lemma 13): ' + (D.sym ? 'yes' : 'NO') + '; height ' + D.height + '. ';
    var plots = [linePlot(n, m, t), pathPlot(w)];
    var rows = [['C(n), sorted', D.cs.slice(0, 60).join(', ') + (D.cs.length > 60 ? ' …' : '')]];
    var bad = !D.ok_C || !D.dyck || !D.sym;
    if (D.oneprime) {
      var e = fac[0][1], Nn = D.oneprime.N;
      txt += 'One prime: by Corollary 3.3(a) the word is O_' + (e + 1) + '(N) with N = min(⌊log t / log p⌋, ' + e + ') = ' + Nn +
        ', the word whose j-th “)” is preceded by min(' + (e + 1) + ', N + j) letters “(”. ';
      txt += 'Check: O_' + (e + 1) + '(' + Nn + ') ' + (D.oneprime.same ? '=' : '≠ (error)') + ' the word. ';
      rows.push(['cell (one prime)', 'N = ' + Nn + ' of 0 … ' + e]);
      bad = bad || !D.oneprime.same;
    } else if (D.twoprimes) {
      var T = D.twoprimes, a = T.a, b = T.b;
      txt += 'Two primes, pattern p^' + a + ' p\'^' + b + ' with r = ' + T.r + ' (exponent a = ' + a + ') and s = ' + T.s +
        ' (exponent b = ' + b + '): in units of log s, Λ = log t / log s and θ = log r / log s. The cell of n is given by the ' +
        'clipped vector c = (c_−' + a + ', …, c_' + a + ') = (' + T.c.join(', ') + '), c_h = clip⌊Λ + hθ⌋, computed exactly ' +
        '(s^ρ < t·r^h, BigInt). Z(c) of Section 6, Step 1 ' + (T.same ? 'equals' : 'DIFFERS FROM (error)') +
        ' C(n), so the word depends only on the cell. ';
      plots.push(cellPlot(a, b, BigInt(T.r), BigInt(T.s), t, T.c));
      rows.push(['cell (two primes): c = (c_−a … c_a)', '(' + T.c.join(', ') + ')']);
      bad = bad || !T.same;
    } else if (fac.length >= 3) {
      var lt = blog(t), x = fac.map(function (q) { return (blog(q[0]) / lt).toFixed(4); });
      txt += fac.length + ' primes: the cell is that of the point x = (log p_i / log t) = (' + x.join(', ') + ') in the ' +
        'arrangement A_f of the hyperplanes α·x = 1; the word only sees the comparisons d < t·d\', which C(n) counts exactly. ';
      rows.push(['point x = (log p_i / log t)', x.join(', ')]);
    }
    if (D.finest) txt += 'By Theorem 3.1 this word is also a word of the finest pattern (' + D.finest.join(', ') + ') of k = ' + k + '.';
    var fig3d = D.oneprime ? fig3dOnePrime(fac[0][0], fac[0][1], D.oneprime.N, n) :
                D.twoprimes ? fig3dTwoPrimes(D.twoprimes, t, n) :
                fac.length === 3 ? fig3dThreePrimes(fac, t, n) : fig3dLetters(n, m, t, w);
    return { text: txt, plots: plots, fig3d: fig3d, table: table(['', 'value'], rows), csv: { head: ['', 'value'], rows: rows },
             bad: bad };
  }

  function randInt(lo, hi) { return lo + Math.floor(Math.random() * (hi - lo + 1)); }
  function pick(xs) { return xs[Math.floor(Math.random() * xs.length)]; }
  function randomWord() {
    var c1 = randInt(2, 1000000);
    var c2 = BigInt(Math.pow(2, randInt(0, 6))) * N.bpow(BigInt(pick([3, 5, 7, 11, 13])), randInt(1, 4)) *
             N.bpow(BigInt(pick([17, 19, 23, 29])), randInt(1, 6));
    return { n: String(pick([BigInt(c1), c2])) };
  }

  // ----------------------------------------------------------------------------------------------- the cells lab
  var VIRIDIS = ['#440154', '#3B528B', '#21918C', '#5EC962', '#FDE725'], WR0 = 0.45, WR1 = 1.0;
  function wrColor(x) {  // W/R in [WR0, WR1] -> a colour of the viridis stops (drawing only)
    var u = Math.max(0, Math.min(1, (x - WR0) / (WR1 - WR0))) * (VIRIDIS.length - 1), i = Math.min(VIRIDIS.length - 2, Math.floor(u)), f = u - i;
    var c0 = VIRIDIS[i], c1 = VIRIDIS[i + 1], out = '#';
    for (var k = 1; k < 7; k += 2) {
      var v = Math.round(parseInt(c0.slice(k, k + 2), 16) * (1 - f) + parseInt(c1.slice(k, k + 2), 16) * f);
      out += (v < 16 ? '0' : '') + v.toString(16);
    }
    return out;
  }

  /* 3D: R(a′,b)/(C_a′ b²) over (a′, b), a′ = 1 … 6, b ≤ min(b_max, LIMIT[a′]); colour W/R. Rows of the chosen a are
     the ones the lab already computed (Rs, Ws); the others are recounted here, exactly. */
  function fig3dCells(a, bmax, Rs, Ws) {
    var rows = {}, bad = 0, n = 0, B = 1, vmax = 1;
    for (var ap = 1; ap <= 6; ap++) {
      var Ca = N.Ca(ap), CaF = Number(Ca.n) / Number(Ca.d), row = [];
      for (var b = 1; b <= Math.min(bmax, N.LIMIT[ap]); b++) {
        var R, W;
        if (ap === a) { R = Rs[b - 1]; W = Ws[b - 1]; }
        else { var r = N.cellRow(ap, b); R = r.Rc; W = r.Wc; bad += r.ok ? 0 : 1; }
        n++;
        var v = W / (CaF * b * b);
        vmax = Math.max(vmax, v); B = Math.max(B, b);
        row.push({ b: b, v: v, wr: W / R });
      }
      rows[ap] = { Ca: Ca, CaF: CaF, row: row };
    }
    var S = 10, kz = 4.5 / vmax;
    function P(ap, b, v) { return [(ap - 1) / 5 * S, (b - 1) / Math.max(1, B - 1) * S, v * kz]; }
    var items = [];
    for (ap = 1; ap < 6; ap++) {  // a strip of surface between rows a′ and a′ + 1, as long as the shorter one
      var r0 = rows[ap].row, r1 = rows[ap + 1].row, len = Math.min(r0.length, r1.length);
      if (len < 2) continue;
      items.push({ type: 'surface', opacity: 0.75,
                   grid: [r0.slice(0, len).map(function (o) { return P(ap, o.b, o.v); }), r1.slice(0, len).map(function (o) { return P(ap + 1, o.b, o.v); })],
                   colors: [r0.slice(0, len).map(function (o) { return wrColor(o.wr); }), r1.slice(0, len).map(function (o) { return wrColor(o.wr); })],
                   name: items.length ? '' : 'W(a,b)/(C_a b²) over (a, b), coloured by W/R' });
    }
    var lim = [], other = [], otherC = [], mine = [], mineC = [], nUp = 0, nLo = 0;
    for (ap = 1; ap <= 6; ap++) {
      var rw = rows[ap].row, bl = rw[rw.length - 1].b;
      rw.forEach(function (o) {
        if (ap === a) { mine.push(P(ap, o.b, o.v)); mineC.push(wrColor(o.wr)); }
        else { other.push(P(ap, o.b, o.v)); otherC.push(wrColor(o.wr)); }
      });
      if (bl < 2) continue;
      // the leading coefficient of W(a,·) lies in [2/3, C_a] (Corollary «degree 2»): in this height, [2/(3C_a), 1]
      lim.push({ type: 'curve', points: [P(ap, 1, 1), P(ap, bl, 1)], color: GRIS, dash: true, width: 1.4,
                 name: nUp++ ? '' : 'upper bound C_a of the leading coefficient of W (level 1)' });
      lim.push({ type: 'curve', points: [P(ap, 1, 2 / (3 * rows[ap].CaF)), P(ap, bl, 2 / (3 * rows[ap].CaF))], color: '#B0B0B0', dash: true, width: 1.2,
                 name: nLo++ ? '' : 'lower bound 2/3 (level 2/(3C_a))' });
      if (ap <= 2) lim.push({ type: 'curve', points: [P(ap, 1, ap === 1 ? 0.9 : 1), P(ap, bl, ap === 1 ? 0.9 : 1)], color: BERMELLON, width: 2.4,
                              name: ap === 1 ? 'limit 9/10 for a = 1 (Theorem A: W ~ 9b²/4, C_1 = 5/2)' : 'limit 1 for a = 2 (Theorem B: W ~ 22b²/3 = C_2 b²)' });
    }
    items = items.concat(lim);
    if (other.length) items.push({ type: 'points', points: other, colors: otherC, size: 4, name: 'exact values, other a' });
    items.push({ type: 'points', points: mine, colors: mineC, marker: 'star', size: 8, name: 'exact values, a = ' + a + ' (the table below)' });
    var ser = [];
    for (ap = 1; ap <= 6; ap++) {
      var rr = rows[ap].row;
      ser.push({ name: 'a = ' + ap + (ap === a ? ' (chosen)' : ''), x: rr.map(function (o) { return o.b; }), y: rr.map(function (o) { return o.v; }),
                 mode: rr.length > 1 ? 'line' : 'points', color: PALETTE[ap - 1], size: 4 });
    }
    ser.push({ name: 'level 1 (C_a; limit for a = 2)', x: [1, B], y: [1, 1], mode: 'line', color: GRIS });
    ser.push({ name: 'level 9/10 (limit for a = 1)', x: [1, B], y: [0.9, 0.9], mode: 'line', color: BERMELLON });
    var flat2d = svgPlot(ser, { title: 'Seen from the side: W(a,b)/(C_a b²) against b, one line per a', xlabel: 'b', ylabel: 'W/(C_a b²)', width: 380, height: 280 });
    var spec = { kind: '3d', axes: ['a (1 … 6)', 'b (1 … ' + B + ')', 'W/(C_a b²)'], items: items, zoomOut: 1, flat: flat2d,
                 colorbar: { label: 'W/R', stops: [['0.45', VIRIDIS[0]], ['0.59', VIRIDIS[1]], ['0.73', VIRIDIS[2]], ['0.86', VIRIDIS[3]], ['1', VIRIDIS[4]]] },
                 title: 'Words per b², relative to C_a: W(a,b)/(C_a b²) for a = 1 … 6, b ≤ ' + bmax + ' (largest ' + vmax.toFixed(2) +
                        ', at b = 1; C_1 = 5/2, …, C_6 = ' + N.qstr(N.Ca(6)) + '). Limits: 9/10 (a = 1) and 1 (a = 2) by Theorems A and B; ' +
                        'open for a ≥ 3, between the dashed bounds. Colour: words per cell W/R' };
    return { spec: spec, bad: bad, n: n };
  }

  function runCells(v) {
    var a = String(v.a).trim(), bmax = String(v.bmax).trim();
    if (!/^-?\d+$/.test(a) || !/^-?\d+$/.test(bmax)) return { error: 'a and b_max must be integers.' };
    a = Number(a); bmax = Number(bmax);
    if (!N.LIMIT[a]) return { error: 'Choose 1 ≤ a ≤ 6.' };
    if (bmax < 1 || bmax > N.LIMIT[a])
      return { error: 'For a = ' + a + ' choose 1 ≤ b_max ≤ ' + N.LIMIT[a] + ' (the exact recount grows like b² a² slopes).' };
    var rows = [], bs = [], Rs = [], Ws = [], ratio = [], bad = 0;
    for (var b = 1; b <= bmax; b++) {
      var r = N.cellRow(a, b);
      bad += r.ok ? 0 : 1;
      bs.push(b); Rs.push(r.Rc); Ws.push(r.Wc); ratio.push(r.Wc / r.Rc);
      rows.push([b, r.Rf, r.Rc, r.Wc, r.closed === null ? '—' : r.closed, r.Rc - r.Wc, (r.Wc / r.Rc).toFixed(4), r.ok ? 'OK' : 'DIFFERS']);
    }
    var Ca = N.Ca(a), CaF = Number(Ca.n) / Number(Ca.d);
    var fig1 = svgPlot([{ name: 'R(a,b): cells (exact recount; the formula of Theorem 5.1 agrees: ' + (bad ? 'NO' : 'yes') + ')',
                          x: bs, y: Rs, mode: 'line', color: GRIS },
                        { name: 'W(a,b): words (distinct Z(c))', x: bs, y: Ws, mode: 'line', color: AZUL },
                        { name: 'C_a b², C_a = ' + N.qstr(Ca), x: bs, y: bs.map(function (b) { return CaF * b * b; }), mode: 'line', color: VERDE }],
                       { title: 'a = ' + a + ': cells and words, b = 1 … ' + bmax, xlabel: 'b', ylabel: 'count' });
    var lim = { 1: 0.9, 2: 1.0 }[a];
    var ser = [{ name: 'W(a,b)/R(a,b), exact', x: bs, y: ratio, mode: 'line', color: AZUL },
               { name: '', x: bs, y: ratio, mode: 'points', color: AZUL, size: 3 }];
    if (lim) ser.push({ name: 'limit ' + (a === 1 ? '9/10' : '1') + ' from Theorems ' + (a === 1 ? 'A' : 'B') + ' (Remark 9.5)',
                        x: bs, y: bs.map(function () { return lim; }), mode: 'line', color: BERMELLON });
    var fig2 = svgPlot(ser, { title: 'Words per cell, a = ' + a, xlabel: 'b', ylabel: 'W/R' });
    var txt = 'a = ' + a + ', b = 1 … ' + bmax + '. Every R(a,b) of the exact recount equals the formula of Theorem 5.1' +
      (bad ? ' — EXCEPT in ' + bad + ' rows (see the table)' : '') + '. ';
    txt += 'C_a = Σ_{q≤2a} (2a+1−q) φ(q)/q = ' + N.qstr(Ca) + ' ≈ ' + CaF.toFixed(4) + ' (Corollary 5.2), against 12a²/π² ≈ ' +
      (12 * a * a / (Math.PI * Math.PI)).toFixed(4) + '. ';
    if (a === 1) txt += 'For a = 1 the column «closed form» is Theorem A, W(1,b) = ⌊(9b² + 8b + 12)/4⌋ (b ≥ 2). ';
    else if (a === 2) txt += 'For a = 2 it is Theorem B, W(2,b) = (44b² + 19b + e_{b mod 6})/6 (b ≥ 3), and R(2,b) is also compared with Lemma 9.2. ';
    else txt += 'For a ≥ 3 the paper has no closed form for W(a,b) (Question 11.1 for a = 3). ';
    txt += 'W counts distinct multisets Z(c), which determine the word (Section 6, Step 1). All counts are exact (BigInt rationals).';
    var F = fig3dCells(a, bmax, Rs, Ws);
    txt += ' The 3D figure recounts R and W for every a′ = 1 … 6 and b ≤ min(b_max, its limit) (' + F.n + ' pairs; Theorem 5.1 ' +
      (F.bad ? 'FAILS in ' + F.bad + ' of them' : 'agrees in all') + ').';
    var G = fig3dClassesA1(a === 1 ? Math.min(8, Math.max(2, bmax)) : 3), gbad = 0;
    G.info.forEach(function (C) { if (!C.same || C.WA !== C.W || C.nOther) gbad++; });
    txt += ' The second 3D figure (the paper’s Figure 6, a = 1, b = 2 … 8 on its slider) groups the exact cells of N.cells(1, b) ' +
      'by word: every class of two or more cells is O(s) or Q(τ,d) ' + (gbad ? '— NOT in ' + gbad + ' values of b' : 'for every b, W(1,b) ' +
      'equals Theorem A and the polygons drawn carry exactly the exact cells') + '.';
    return { text: txt, plots: [fig1, fig2], fig3d: [F.spec, G.spec], bad: bad > 0 || F.bad > 0 || gbad > 0,
             table: table(['b', 'R formula', 'R recount', 'W recount', 'closed form', 'R − W', 'W/R', 'check'], rows),
             csv: { head: ['b', 'R formula', 'R recount', 'W recount', 'closed form', 'R - W', 'W/R', 'check'], rows: rows } };
  }

  function randomCells() { var a = randInt(1, 4); return { a: String(a), bmax: String(randInt(1, N.LIMIT[a])) }; }

  // ------------------------------------------------------------------------------------------------ the wiring
  var LABS = { word: { run: runWord, random: randomWord }, cells: { run: runCells, random: randomCells },
               mech: { run: runMech, random: randomMech } };

  function values(box) {
    var v = {};
    box.querySelectorAll('[data-dk-in]').forEach(function (el) { v[el.getAttribute('data-dk-in')] = el.value; });
    return v;
  }
  function setValues(box, v) {
    Object.keys(v).forEach(function (k) { var el = box.querySelector('[data-dk-in="' + k + '"]'); if (el) el.value = v[k]; });
  }

  /* Under the result, as in Lemmario's Pyodide labs (lab.js): the table as CSV and a link that reopens the lab with
     these inputs (?lab=<node>&<input>=<value>…#<node>, read back by wire()). */
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
      a.download = 'dyck-divisors-' + box.getAttribute('data-dk-lab') + '.csv';
      document.body.appendChild(a); a.click(); a.remove();
    });
    p.querySelector('.lm-link').addEventListener('click', function () {
      // the page without its query and anchor: works the same from file:// and on the web
      var url = location.href.split(/[?#]/)[0] + '?' + new URLSearchParams(Object.assign({ lab: node }, values(box))) + '#' + node;
      msg.setAttribute('data-url', url);  // the link made, also for captura_3d.py
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
    var status = box.querySelector('.dk-status'), text = box.querySelector('.dk-text'), state = box.querySelector('.lm-state'),
        plots = box.querySelector('.dk-plots'), tab = box.querySelector('.dk-tab');
    status.className = 'dk-status'; status.textContent = 'Computing…';
    if (state) state.textContent = '⏳ computing…';
    var t0 = performance.now(), res;
    try { res = lab.run(values(box)); } catch (e) { res = { error: 'The computation failed: ' + (e && e.message || e) }; }
    var secs = ((performance.now() - t0) / 1000).toFixed(1);
    if (res.error) {  // class «err»: the reader sees the reason, and lemmario review counts it as a failure
      status.className = 'dk-status err'; status.textContent = '⚠️ ' + res.error;
      if (state) state.textContent = '';
      text.textContent = ''; plots.innerHTML = ''; tab.innerHTML = '';
      return;
    }
    if (state) state.textContent = '✅ computed in ' + secs + ' s';
    status.textContent = res.bad ? '⚠️ Done, but a check FAILED (see below).' :
      'Every check passed (exact integer arithmetic, in your browser).';
    if (res.bad) status.className = 'dk-status err';
    text.textContent = res.text;
    plots.innerHTML = slots3d(res.fig3d) + res.plots.join('');
    mount3d(plots, res.fig3d);
    tab.innerHTML = res.table || '';
    tab.appendChild(tools(box, res));
  }

  /* The paper's figure that a lab redraws gets, under it, a button to the lab (like figure_link in lab.js). */
  function openLab(box) {
    for (var e = box; e; e = e.parentElement) if (e.tagName === 'DETAILS') e.open = true;
    box.scrollIntoView({ block: 'start' });
  }
  function figureLink(box) {
    var fig = box.getAttribute('data-dk-figure');
    if (!fig) return;
    document.querySelectorAll('img[data-fig="' + fig + '"]').forEach(function (img) {
      if (img.parentElement.querySelector(':scope > .lm-figlink[data-dk-for="' + fig + '"]')) return;
      var b = document.createElement('button');
      b.type = 'button'; b.className = 'lm-figlink'; b.setAttribute('data-dk-for', fig);
      b.textContent = '🧪 Your own input: the lab →';
      b.addEventListener('click', function () {
        // the lab may live in the other view (Paper / Explore): switch to the view where it is shown
        if (box.offsetParent === null) { var ex = document.querySelector('button[data-v="explore"]'); if (ex) ex.click(); }
        openLab(box);
      });
      img.insertAdjacentElement('afterend', b);
    });
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
    // a link made by «copy a link with these values»: ?lab=<node>&<input>=<value>…
    var P = new URLSearchParams(location.search), linked = P.get('lab') === box.getAttribute('data-dk-node');
    if (linked) box.querySelectorAll('[data-dk-in]').forEach(function (el) {
      var k = el.getAttribute('data-dk-in');
      if (P.has(k)) el.value = P.get(k);
    });
    figureLink(box);
    box.querySelectorAll('[data-dk-example]').forEach(function (btn) {
      btn.addEventListener('click', function () { setValues(box, JSON.parse(btn.getAttribute('data-dk-example'))); go(); });
    });
    box.querySelectorAll('[data-dk-in]').forEach(function (el) {
      el.addEventListener('keydown', function (e) { if (e.key === 'Enter') { e.preventDefault(); go(); } });
    });
    show(box, lab);  // initial state at load, no click needed
    if (linked) setTimeout(function () { openLab(box); }, 300);
  }

  function start() {
    if (!N) throw new Error('nucleo.js did not load (window.DyckNucleo is missing)');
    document.querySelectorAll('[data-dk-lab]').forEach(wire);
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
