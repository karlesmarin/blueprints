/* Lemmario: 3D figures of the labs, drawn on a canvas, without libraries. A lab returns, among its plots,
   {kind: '3d', title, axes: ['a', 'p', 'q'], items: [...], slider: {label, values: [...], items: [[...], ...]},
   figure, live}. An item is {type: 'surface', grid: [[[x, y, z], ...], ...], color, opacity}, {type: 'curve',
   points: [[x, y, z], ...], color, dash, width} or {type: 'points', points: [[x, y, z], ...], color, marker:
   'star' | 'dot', size, opacity}; each may carry a name for the legend. The slider shows one list of items per value
   (▶ runs it); with cumulative: true it shows the lists up to the value, a cloud that grows ({current: true}: only at
   its own value).
   Drag to turn the figure. Registered as window.LemmarioFigures['3d'] (lab.js mounts it). */
(function () {
  var REDUCED = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  function esc(s) { return String(s).replace(/[&<>]/g, function (c) { return {'&': '&amp;', '<': '&lt;', '>': '&gt;'}[c]; }); }

  function rgb(hex) {
    var h = hex.replace('#', '');
    if (h.length === 3) h = h.split('').map(function (c) { return c + c; }).join('');
    return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16)];
  }
  function rgba(c, a, light) {  // light in [0, 1]: 0 the colour itself, towards 1 lighter
    var l = light || 0;
    return 'rgba(' + c.map(function (x) { return Math.round(x + (255 - x) * l); }).join(',') + ',' + a + ')';
  }

  // every [x, y, z] of an item (a surface's grid, a curve or a set of points)
  function coords(item) {
    return item.type === 'surface' ? [].concat.apply([], item.grid) : item.points;
  }
  function bounds(spec) {
    var lo = [Infinity, Infinity, Infinity], hi = [-Infinity, -Infinity, -Infinity];
    var lists = [spec.items || []].concat(spec.slider ? spec.slider.items : []);
    lists.forEach(function (items) {
      items.forEach(function (it) {
        coords(it).forEach(function (v) {
          for (var i = 0; i < 3; i++) { lo[i] = Math.min(lo[i], v[i]); hi[i] = Math.max(hi[i], v[i]); }
        });
      });
    });
    return {lo: lo, hi: hi};
  }

  // the camera: turn by yaw around the vertical (third) axis, then tilt by pitch; one scale for the three axes,
  // so the figure keeps its true shape, and a mild perspective
  function camera(b, yaw, pitch) {
    var c = [0, 1, 2].map(function (i) { return (b.lo[i] + b.hi[i]) / 2; });
    var half = Math.max(b.hi[0] - b.lo[0], b.hi[1] - b.lo[1], b.hi[2] - b.lo[2]) / 2 || 1;
    var cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    return function (v) {
      var x = (v[0] - c[0]) / half, y = (v[1] - c[1]) / half, z = (v[2] - c[2]) / half;
      var x1 = x * cy - y * sy, y1 = x * sy + y * cy;
      var depth = y1 * cp - z * sp, f = 1 / (1 + 0.12 * depth);
      return [x1 * f, (z * cp + y1 * sp) * f, depth];
    };
  }

  // the primitives of a list of items, each with its depth (far first when sorted)
  function primitives(items, P) {
    var out = [];
    items.forEach(function (it, k) {
      var col = rgb(it.color || '#555'), op = it.opacity === undefined ? 0.2 : it.opacity;
      if (it.type === 'surface') {
        var g = it.grid.map(function (row) { return row.map(P); });
        for (var i = 0; i + 1 < g.length; i++) {
          for (var j = 0; j + 1 < g[i].length; j++) {
            var q = [g[i][j], g[i][j + 1], g[i + 1][j + 1], g[i + 1][j]];
            var w = [it.grid[i][j], it.grid[i][j + 1], it.grid[i + 1][j]];
            // light from the normal's vertical part: a cue for the shape, not a model of light
            var u = [0, 1, 2].map(function (m) { return w[1][m] - w[0][m]; });
            var v = [0, 1, 2].map(function (m) { return w[2][m] - w[0][m]; });
            var n = [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]];
            var len = Math.hypot(n[0], n[1], n[2]) || 1;
            out.push({kind: 'quad', pts: q, depth: (q[0][2] + q[1][2] + q[2][2] + q[3][2]) / 4, col: col, op: op,
                      light: 0.15 + 0.45 * Math.abs(n[2] / len)});
          }
        }
      } else if (it.type === 'curve') {
        var p = it.points.map(P);
        for (var s = 0; s + 1 < p.length; s++) {
          out.push({kind: 'seg', a: p[s], b: p[s + 1], depth: (p[s][2] + p[s + 1][2]) / 2 - 0.01, col: col,
                    width: it.width || 2.6, dash: it.dash});
        }
      } else {
        it.points.map(P).forEach(function (p) {
          out.push({kind: 'mark', at: p, depth: p[2] - 0.05, col: col, marker: it.marker || 'dot', size: it.size,
                    op: it.opacity === undefined ? 1 : it.opacity});
        });
      }
    });
    return out.sort(function (x, y) { return y.depth - x.depth; });
  }

  function star(ctx, x, y, r) {
    ctx.beginPath();
    for (var i = 0; i < 10; i++) {
      var a = -Math.PI / 2 + i * Math.PI / 5, rr = i % 2 ? r * 0.45 : r;
      ctx[i ? 'lineTo' : 'moveTo'](x + rr * Math.cos(a), y + rr * Math.sin(a));
    }
    ctx.closePath();
  }

  function legend(items) {
    return items.filter(function (it) { return it.name; }).map(function (it) {
      var c = it.color || '#555', sw;
      if (it.type === 'surface') sw = '<span class="l3-sw" style="background:' + rgba(rgb(c), 0.35) + ';border:1px solid ' + c + '"></span>';
      else if (it.type === 'curve') sw = '<span class="l3-sw" style="height:0;border-top:3px ' + (it.dash ? 'dashed' : 'solid') + ' ' + c + '"></span>';
      else sw = '<span style="color:' + c + '">' + (it.marker === 'star' ? '★' : '●') + '</span>';
      return '<span class="l3-it">' + sw + ' ' + esc(it.name) + '</span>';
    }).join('');
  }

  function mount(host, spec) {
    var sl = spec.slider, nf = sl ? sl.values.length : 0, frame = sl ? (sl.start !== undefined ? sl.start : nf - 1) : 0;
    host.innerHTML = '<div class="l3"><div class="l3-title">' + esc(spec.title || '') + '</div>' +
      '<canvas aria-label="' + esc(spec.title || '3D figure') + '"></canvas>' +
      '<div class="l3-bar">' + (sl ? '<button type="button" class="l3-play" title="run ' + esc(sl.label) + '">▶</button>' +
      '<input type="range" min="0" max="' + (nf - 1) + '" value="' + frame + '"> <span class="l3-val"></span>' : '') +
      '<button type="button" class="l3-zin" title="zoom in">＋</button><button type="button" class="l3-zout" title="zoom out">－</button>' +
      '<button type="button" class="l3-reset" title="initial view">⟲</button><span class="l3-hint">drag to turn</span></div>' +
      '<div class="l3-legend"></div></div>';
    var cv = host.querySelector('canvas'), ctx = cv.getContext('2d'), b = bounds(spec);
    var range = host.querySelector('input[type=range]'), val = host.querySelector('.l3-val'), lg = host.querySelector('.l3-legend');
    var V0 = {yaw: -0.55, pitch: 0.32, zoom: 1}, view = Object.assign({}, V0);
    var auto = !REDUCED, playing = false, dirty = true, last = 0, width = 0;

    // a cumulative slider adds up its steps (a cloud that grows), except the items marked {current: true}, which
    // belong to their own step only (e.g. a bound that changes with it)
    function items() {
      if (!sl) return spec.items || [];
      if (!sl.cumulative) return (spec.items || []).concat(sl.items[frame]);
      var out = [];
      for (var i = 0; i <= frame; i++) {
        out = out.concat(sl.items[i].filter(function (it) { return !it.current || i === frame; }));
      }
      return out.concat(spec.items || []);  // the fixed items last: on top in the legend order and drawn by depth anyway
    }
    function showFrame() {
      if (sl) val.textContent = sl.label + ' = ' + sl.values[frame];
      lg.innerHTML = legend(items());
      dirty = true;
    }

    function axes(P, S) {  // the box of the data, faint, and the names of the axes on three of its edges
      var lo = b.lo, hi = b.hi, C = [];
      for (var i = 0; i < 8; i++) C.push([i & 1 ? hi[0] : lo[0], i & 2 ? hi[1] : lo[1], i & 4 ? hi[2] : lo[2]]);
      ctx.strokeStyle = 'rgba(120,130,140,.35)'; ctx.lineWidth = 1; ctx.setLineDash([]);
      [[0, 1], [0, 2], [0, 4], [1, 3], [1, 5], [2, 3], [2, 6], [3, 7], [4, 5], [4, 6], [5, 7], [6, 7]].forEach(function (e) {
        var a = S(P(C[e[0]])), c = S(P(C[e[1]]));
        ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(c[0], c[1]); ctx.stroke();
      });
      ctx.fillStyle = '#333'; ctx.font = 'italic 14px "Times New Roman", serif'; ctx.textAlign = 'center';
      var names = spec.axes || ['x', 'y', 'z'];
      [[0, 1, 0], [0, 2, 1], [0, 4, 2]].forEach(function (e) {
        var m = S(P(C[e[0]].map(function (x, i) { return (x + C[e[1]][i]) / 2; })));
        ctx.fillText(names[e[2]], m[0] + (e[2] === 2 ? -12 : 0), m[1] + (e[2] === 2 ? 0 : 16));
      });
    }

    function draw() {
      var w = Math.min(host.clientWidth || 560, 680), h = Math.round(w * 0.72), r = window.devicePixelRatio || 1;
      if (w !== width) { width = w; cv.width = w * r; cv.height = h * r; cv.style.width = w + 'px'; cv.style.height = h + 'px'; }
      ctx.setTransform(r, 0, 0, r, 0, 0);
      ctx.clearRect(0, 0, w, h);
      var P = camera(b, view.yaw, view.pitch), sc = 0.36 * w * view.zoom;
      function S(p) { return [w / 2 + p[0] * sc, h / 2 - p[1] * sc]; }
      axes(P, S);
      primitives(items(), P).forEach(function (o) {
        if (o.kind === 'quad') {
          ctx.beginPath();
          o.pts.forEach(function (p, i) { var s = S(p); ctx[i ? 'lineTo' : 'moveTo'](s[0], s[1]); });
          ctx.closePath();
          ctx.fillStyle = rgba(o.col, o.op, o.light); ctx.fill();
          ctx.strokeStyle = rgba(o.col, Math.min(1, o.op * 2.2)); ctx.lineWidth = 0.5; ctx.setLineDash([]); ctx.stroke();
        } else if (o.kind === 'seg') {
          var a = S(o.a), c = S(o.b);
          ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(c[0], c[1]);
          ctx.strokeStyle = rgba(o.col, 1); ctx.lineWidth = o.width; ctx.lineCap = 'round';
          ctx.setLineDash(o.dash ? [5, 5] : []); ctx.stroke();
        } else {
          var m = S(o.at), size = o.size || (o.marker === 'star' ? 9 : 5);
          if (o.marker === 'star') star(ctx, m[0], m[1], size); else { ctx.beginPath(); ctx.arc(m[0], m[1], size, 0, 2 * Math.PI); }
          ctx.fillStyle = rgba(o.col, o.op); ctx.fill();
          if (size >= 4) { ctx.strokeStyle = '#fff'; ctx.lineWidth = 1.4; ctx.setLineDash([]); ctx.stroke(); }  // small: a cloud
        }
      });
      dirty = false;
    }

    // turning: a drag (mouse or finger; a vertical finger drag still scrolls the page, see touch-action in the css)
    var drag = null;
    cv.addEventListener('pointerdown', function (e) { drag = [e.clientX, e.clientY]; auto = false; cv.setPointerCapture(e.pointerId); });
    cv.addEventListener('pointermove', function (e) {
      if (!drag) return;
      view.yaw -= (e.clientX - drag[0]) * 0.01;
      view.pitch = Math.max(-1.45, Math.min(1.45, view.pitch + (e.clientY - drag[1]) * 0.01));
      drag = [e.clientX, e.clientY]; dirty = true;
    });
    ['pointerup', 'pointercancel'].forEach(function (n) { cv.addEventListener(n, function () { drag = null; }); });
    host.querySelector('.l3-zin').onclick = function () { view.zoom = Math.min(3, view.zoom * 1.2); dirty = true; };
    host.querySelector('.l3-zout').onclick = function () { view.zoom = Math.max(0.4, view.zoom / 1.2); dirty = true; };
    host.querySelector('.l3-reset').onclick = function () { view = Object.assign({}, V0); dirty = true; };
    if (sl) {
      range.addEventListener('input', function () { frame = Number(range.value); playing = false; play.textContent = '▶'; showFrame(); });
      var play = host.querySelector('.l3-play');
      play.onclick = function () {
        playing = !playing; play.textContent = playing ? '⏸' : '▶';
        if (playing && frame === nf - 1) { frame = 0; range.value = 0; showFrame(); }
      };
    }

    function tick(now) {
      if (!cv.isConnected) return;  // the lab drew a new result: this figure is gone, stop
      if (auto) { view.yaw += 0.003; dirty = true; }
      if (playing && now - last > 140) {
        last = now;
        if (frame < nf - 1) { frame += 1; range.value = frame; showFrame(); } else { playing = false; play.textContent = '▶'; }
      }
      if (dirty || (host.clientWidth && Math.min(host.clientWidth, 680) !== width)) draw();
      requestAnimationFrame(tick);
    }
    showFrame();
    draw();
    requestAnimationFrame(tick);
  }

  var css = document.createElement('style');
  css.textContent = '.l3{margin:.5em 0;font:13px Arial,sans-serif}.l3-title{font-size:13px;margin:.2em 0 .3em;text-align:center}' +
    '.l3 canvas{display:block;max-width:100%;background:#fff;border:1px solid #dde3ea;border-radius:6px;cursor:grab;touch-action:pan-y}' +
    '.l3 canvas:active{cursor:grabbing}.l3-bar{display:flex;flex-wrap:wrap;gap:.4em;align-items:center;margin:.35em 0}' +
    '.l3-bar button{padding:.1em .6em;cursor:pointer;border:1px solid #ef6c00;background:#fff;border-radius:14px}' +
    '.l3-bar input[type=range]{flex:1;min-width:120px;max-width:280px}.l3-val{min-width:5.5em;font-variant-numeric:tabular-nums}' +
    '.l3-hint{color:#777;font-size:12px}.l3-legend{display:flex;flex-wrap:wrap;gap:.3em 1em;font-size:12px}' +
    '.l3-it{display:inline-flex;align-items:center;gap:.35em}.l3-sw{display:inline-block;width:18px;height:10px;border-radius:2px}';
  document.head.appendChild(css);
  window.LemmarioFigures = window.LemmarioFigures || {};
  window.LemmarioFigures['3d'] = {mount: mount};
})();
