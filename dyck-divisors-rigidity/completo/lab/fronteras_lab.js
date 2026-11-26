// Explore the 25 explicitly listed degeneracy lines of the a=3 deep-cell result.
// Geometry only: the numerical distance is illustrative, not the unspecified constant C of the theorem.
(function () {
  'use strict';
  var L = [];
  for (var h = -3; h <= 3; h++) for (var c = -1; c <= 1; c++)
    L.push({ A: 1, B: h, C: c, name: 'λ ' + (h < 0 ? '− ' + (-h) : '+ ' + h) + 'μ = ' + c });
  for (var k = 1; k <= 3; k++) L.push({ A: 0, B: k, C: 1, name: k + 'μ = 1' });
  L.push({ A: 0, B: 1, C: 0, name: 'μ = 0' });
  function dist(l, x, y) { return Math.abs(l.A * x + l.B * y - l.C) / Math.hypot(l.A, l.B); }
  function nearest(x, y) {
    var d = Infinity, at = -1;
    L.forEach(function (l, i) { var v = dist(l, x, y); if (v < d) { d = v; at = i; } });
    return { d: d, at: at };
  }
  function segment(l) {
    var p = [];
    function add(x, y) {
      if (x < -1e-9 || x > 1 + 1e-9 || y < -1e-9 || y > 1 + 1e-9) return;
      if (!p.some(function (q) { return Math.hypot(q[0] - x, q[1] - y) < 1e-8; })) p.push([x, y]);
    }
    if (l.B) { add(0, l.C / l.B); add(1, (l.C - l.A) / l.B); }
    if (l.A) { add(l.C / l.A, 0); add((l.C - l.B) / l.A, 1); }
    if (p.length < 2) return null;
    var best = null, len = -1;
    p.forEach(function (u) { p.forEach(function (v) { var d = Math.hypot(u[0] - v[0], u[1] - v[1]);
      if (d > len) { len = d; best = [u, v]; } }); });
    return best;
  }
  function flat(x, y, near) {
    var W = 500, H = 510, pad = 36, size = 430;
    var X = function (v) { return pad + v * size; }, Y = function (v) { return pad + (1 - v) * size; };
    var s = ['<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="2D map of the 25 degeneracy lines">',
      '<text x="250" y="20" text-anchor="middle" font-size="14" font-weight="700">2D: the lines in the unit box</text>',
      '<rect x="' + pad + '" y="' + pad + '" width="' + size + '" height="' + size + '" fill="#f8fbfd" stroke="#9ba9b5"/>'];
    L.forEach(function (l, i) { var p = segment(l); if (!p) return;
      s.push('<path d="M' + X(p[0][0]).toFixed(1) + ',' + Y(p[0][1]).toFixed(1) + ' L' +
        X(p[1][0]).toFixed(1) + ',' + Y(p[1][1]).toFixed(1) + '" stroke="' +
        (i === near ? '#D55E00' : '#a8b8c5') + '" stroke-width="' + (i === near ? 2.4 : .9) + '"/>');
    });
    s.push('<circle cx="' + X(x).toFixed(1) + '" cy="' + Y(y).toFixed(1) + '" r="5" fill="#0072B2" stroke="#fff" stroke-width="1.4"/>',
      '<text x="250" y="497" text-anchor="middle" font-size="12">λ = Λ/b →</text>',
      '<text x="10" y="260" font-size="12" transform="rotate(-90 10 260)">μ = θ/b →</text></svg>');
    return s.join('');
  }
  function run(v) {
    var x = Number(v.lambda), y = Number(v.mu), b = Number(v.b);
    if (!Number.isFinite(x) || !Number.isFinite(y) || x < 0 || x > 1 || y < 0 || y > 1 ||
        !Number.isInteger(b) || b < 317 || b > 1000)
      return { error: 'Choose λ and μ in [0,1] and integer b from 317 to 1000.' };
    var n = nearest(x, y), grid = [];
    for (var j = 0; j <= 20; j++) {
      var row = [];
      for (var i = 0; i <= 20; i++) row.push([i / 20, j / 20, 4 * nearest(i / 20, j / 20).d]);
      grid.push(row);
    }
    var spec = { title: '3D: distance terrain over the 25 lines · drag to turn',
      axes: ['λ', 'μ', '4 × distance'],
      items: [{ type: 'surface', grid: grid, color: '#56B4E9', opacity: .65 },
              { type: 'points', points: [[x, y, 4 * n.d]], color: '#D55E00', marker: 'star', size: 12,
                name: 'chosen point' }],
      flat: function () { return flat(x, y, n.at); } };
    var text = 'The paper lists 25 lines in normalized coordinates; the orange line is nearest to your point: ' +
      L[n.at].name + '. Normalized Euclidean distance ≈ ' + n.d.toFixed(5) +
      '; at b=' + b + ' the corresponding distance is ≈ ' + (b * n.d).toFixed(2) +
      '. The 3D height is multiplied by 4 solely for visibility. This map locates the exceptional lines; it does not ' +
      'enumerate cells or supply the unspecified constant C in the deep-cell corollary.';
    var tab = '<div class="dk-tablewrap"><table class="dk-table"><tr><th>Line family</th><th>Count</th></tr>' +
      '<tr><td>λ + hμ = 0, ±1; |h| ≤ 3</td><td>21</td></tr>' +
      '<tr><td>kμ = 1; k = 1,2,3</td><td>3</td></tr><tr><td>μ = 0</td><td>1</td></tr></table></div>';
    return { fig3d: [spec], text: text, table: tab, bad: L.length !== 25 || Math.abs(nearest(0, 0).d) > 1e-12,
      csv: { name: 'a3-degeneracy-lines.csv', head: ['A', 'B', 'C', 'equation'],
        rows: L.map(function (l) { return [l.A, l.B, l.C, l.name]; }) } };
  }
  window.BoundaryLab = { run: run, random: function () {
    return { lambda: (0.05 + 0.9 * Math.random()).toFixed(2), mu: (0.05 + 0.9 * Math.random()).toFixed(2), b: '317' };
  } };
})();
