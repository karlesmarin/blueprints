// The a=2 affine certificate, regenerated from rigidez_a2.jsonl.gz by lab/hacer_certificado.py.
// Exact checks use integer coefficients; floating point is used only to place points on the drawings.
(function () {
  'use strict';
  var D = window.CertDatos;
  var BLUE = '#0072B2', ORANGE = '#D55E00';
  function lattice(b) {
    var out = [];
    for (var m = 1; m <= Math.floor(b / 4); m++)
      for (var n = 1; n < b; n++) if (n > 2 * m && n + 2 * m < b) out.push([n, m]);
    return out;
  }
  function integer(v, lo, hi) {
    var s = String(v).trim();
    return /^\d+$/.test(s) && +s >= lo && +s <= hi ? +s : null;
  }
  function exact(pair, k) {
    if (!D || D.a !== 2 || D.chamber.length !== 3 || pair.clase !== 'no_entera' ||
        pair.k.join() !== ['0', '-' + k + '/3', '0'].join() ||
        pair.M.map(function (r) { return r.join(); }).join(';') !== '1,0,0;0,1,0;0,0,1' ||
        pair.VP.length !== pair.VQ.length) return false;
    return pair.VP.every(function (p, i) {
      var q = pair.VQ[i];
      return p.length === 4 && q.length === 4 && p[0] === q[0] && p[1] === q[1] &&
             p[2] === q[2] && 3 * p[3] === 3 * q[3] - k * q[1];
    });
  }
  function svg2d(b, k, pts) {
    var W = 620, H = 330, L = 46, R = 15, T = 28, B = 40;
    var X = function (n) { return L + n / b * (W - L - R); };
    var Y = function (m) { return H - B - m / (b / 4) * (H - T - B); };
    var s = ['<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="2D chamber section and exact shifted lattice">',
      '<text x="310" y="17" text-anchor="middle" font-size="14" font-weight="700">2D section at b = ' + b + '</text>',
      '<path d="M' + X(0) + ',' + Y(0) + ' L' + X(b) + ',' + Y(0) + ' L' + X(b/2) + ',' + Y(b/4) + ' Z" fill="#dceef8" stroke="' + BLUE + '"/>'];
    pts.forEach(function (p) {
      var x = X(p[0]), y = Y(p[1]), xq = X(p[0] - k / 3);
      s.push('<circle cx="' + x.toFixed(2) + '" cy="' + y.toFixed(2) + '" r="2.8" fill="' + BLUE + '"/>');
      s.push('<path d="M' + (xq - 3).toFixed(2) + ',' + (y - 3).toFixed(2) + ' l6,6 m0,-6 l-6,6" fill="none" stroke="' + ORANGE + '" stroke-width="1.2"/>');
    });
    s.push('<text x="' + X(0) + '" y="' + (H - 8) + '" font-size="12">n →</text>',
      '<text x="8" y="' + (H / 2) + '" font-size="12">m</text>',
      '<circle cx="410" cy="35" r="3" fill="' + BLUE + '"/><text x="418" y="39" font-size="11">integer inputs</text>',
      '<path d="M407,46 l6,6 m0,-6 l-6,6" stroke="' + ORANGE + '" fill="none"/><text x="418" y="51" font-size="11">images n − ' + k + '/3</text>',
      '</svg>');
    return s.join('');
  }
  function run(v) {
    var b = integer(v.b, 12, 48), k = integer(v.k, 1, 2);
    if (b === null || k === null) return { error: 'Choose integer b from 12 to 48 and shift 1/3 or 2/3.' };
    var pair = D.pairs[k], valid = exact(pair, k);
    var layers = [Math.max(8, b - 12), b, Math.min(60, b + 12)].filter(function (x, i, a) { return a.indexOf(x) === i; });
    var items = [], csv = [];
    layers.forEach(function (bb) {
      var p = lattice(bb), poly = [[0, 0, bb], [bb, 0, bb], [bb / 2, 3 * bb / 4, bb]];
      items.push({ type: 'surface', grid: [[poly[0], poly[1]], [poly[2], poly[2]]], color: BLUE, opacity: .11 });
      items.push({ type: 'points', points: p.map(function (q) { return [q[0], 3 * q[1], bb]; }), color: BLUE, size: 4, name: 'integer lattice at b=' + bb });
      items.push({ type: 'points', points: p.map(function (q) { return [q[0] - k/3, 3 * q[1], bb]; }), color: ORANGE, size: 4, name: 'shifted by −' + k + '/3' });
    });
    var pts = lattice(b), inChamber = pts.every(function (p) { return 3 * p[0] - k > 6 * p[1] && 3 * p[0] - k + 6 * p[1] < 3 * b; });
    var noInteger = pts.every(function (p) { return (3 * p[0] - k) % 3 !== 0; });
    pts.forEach(function (p) { csv.push([b, p[0], p[1], 3 * p[0] - k, 3]); });
    var spec = { title: '3D: actual certificate pair ' + pair.P + ' → ' + pair.Q + ' · drag to turn',
      axes: ['n', '3m', 'b'], items: items, flat: function () { return svg2d(b, k, pts); } };
    var ok = valid && inChamber && noInteger && pts.length > 0;
    var text = 'Portable a=2 certificate: pieces ' + pair.P + ' and ' + pair.Q + ', same chamber. ' +
      'All ' + pair.VP.length + ' affine observation coordinates agree identically under (b,n,m) ↦ (b,n−' + k + '/3,m) ' + (valid ? '✓' : '✗') +
      '. At b=' + b + ', ' + pts.length + ' displayed integer chamber points; every shifted point remains in the chamber ' +
      (inChamber ? '✓' : '✗') + ' and has noninteger n because 3n−' + k + ' is not divisible by 3 ' + (noInteger ? '✓' : '✗') +
      '. The point cloud uses chamber inequalities only; it does not assert that every point is generic for either piece. ' +
      'The 3D m-axis is stretched threefold for legibility; the 2D section uses the true coordinates.';
    var table = '<div class="dk-tablewrap"><table class="dk-table"><tr><th>Certificate</th><th>Exact check</th></tr>' +
      '<tr><td>Affine rows</td><td>' + pair.VP.length + ' identities, ' + (valid ? 'all equal' : 'FAILED') + '</td></tr>' +
      '<tr><td>Shift</td><td>n′ = n − ' + k + '/3; denominator 3</td></tr>' +
      '<tr><td>2D section</td><td>' + pts.length + ' lattice points at b = ' + b + '</td></tr></table></div>';
    return { fig3d: [spec], text: text, table: table, bad: !ok,
      csv: { name: 'certificate-a2-b' + b + '-k' + k + '.csv',
        head: ['b', 'n', 'm', 'shifted_n_numerator', 'shifted_n_denominator'], rows: csv } };
  }
  window.CertLab = { run: run, random: function () { return { b: String(12 + Math.floor(Math.random() * 37)),
                                                        k: String(1 + Math.floor(Math.random() * 2)) }; } };
})();
