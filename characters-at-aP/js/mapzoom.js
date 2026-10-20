/* Lemmario: zoom, pan, full screen, sections and dependency highlight for the map of the results (Graphviz SVG).
   Works on every "div.mapa" of the page; no external library. The map stays generated from the data: this only changes
   the view. */
(function () {
  function init(box) {
    var svg = box.querySelector('svg');
    if (!svg || box.dataset.zoom) return;
    box.dataset.zoom = '1';
    var vb0 = (svg.getAttribute('viewBox') || '').split(/[\s,]+/).map(Number);
    if (vb0.length !== 4 || !vb0[2]) {
      var bb = svg.getBBox(); vb0 = [bb.x, bb.y, bb.width, bb.height];
    }
    var vb = vb0.slice();
    svg.setAttribute('viewBox', vb.join(' '));
    // initial height from the map's own shape (a wide map is not put in a tall empty box), within [320px, 85vh]
    function natural() {
      var w = box.clientWidth || 900;
      return Math.max(320, Math.min(window.innerHeight * 0.85, w * vb0[3] / vb0[2])) + 'px';
    }
    svg.style.width = '100%'; svg.style.minWidth = '0'; svg.style.height = natural(); svg.style.cursor = 'grab';
    svg.style.touchAction = 'none';
    function set() { svg.setAttribute('viewBox', vb.join(' ')); }
    // a phone (20-oct, Carles: «los maps en móvil no se ven bien»): the whole map fitted to 390 px is drawn at ~15 %,
    // with 2 px letters. When fitting would go below READABLE, start at a readable scale on the top left of the map
    // (drag or pinch to move; ⟲ still shows the whole map) in a taller box.
    var READABLE = 0.6, w0 = box.clientWidth || 900;
    if (w0 / vb0[2] < 0.45) {
      var hpx = Math.round(window.innerHeight * 0.7);
      svg.style.height = hpx + 'px';
      vb = [vb0[0], vb0[1], w0 / READABLE, hpx / READABLE]; set();
      var hint = document.createElement('div');
      hint.className = 'mz-phone';
      hint.textContent = 'Drag to move · pinch to zoom · ⟲ shows the whole map';
      box.parentNode.insertBefore(hint, box);
    }

    // --- controls -------------------------------------------------------------------------------------------
    var bar = document.createElement('div');
    bar.className = 'mz-bar';
    bar.innerHTML = '<button data-a="in" title="zoom in">＋</button><button data-a="out" title="zoom out">−</button>' +
      '<button data-a="fit" title="whole map">⟲</button><button data-a="full" title="full screen">⛶</button>' +
      '<a class="mz-svg" title="download the map as SVG">⤓ SVG</a><span class="mz-help">wheel or pinch: zoom · drag: move' +
      ' · hover a box: what it uses and what uses it</span><span class="mz-secs"></span>';
    box.parentNode.insertBefore(bar, box);
    var blob = new Blob([new XMLSerializer().serializeToString(svg)], {type: 'image/svg+xml'});
    var dl = bar.querySelector('.mz-svg'); dl.href = URL.createObjectURL(blob); dl.download = 'map.svg';

    function zoom(f, cx, cy) {  // f < 1 zooms in, around (cx, cy) in SVG units
      if (cx === undefined) { cx = vb[0] + vb[2] / 2; cy = vb[1] + vb[3] / 2; }
      var w = vb[2] * f, h = vb[3] * f;
      if (w > vb0[2] * 3 || w < vb0[2] / 40) return;
      vb = [cx - (cx - vb[0]) * f, cy - (cy - vb[1]) * f, w, h]; set();
    }
    function toSvg(ev) {
      var r = svg.getBoundingClientRect();
      var s = Math.max(vb[2] / r.width, vb[3] / r.height);  // preserveAspectRatio meet
      var ox = (r.width - vb[2] / s) / 2, oy = (r.height - vb[3] / s) / 2;
      return [vb[0] + (ev.clientX - r.left - ox) * s, vb[1] + (ev.clientY - r.top - oy) * s, s];
    }
    function fitTo(x, y, w, h) {
      var pad = 0.06 * Math.max(w, h);
      vb = [x - pad, y - pad, w + 2 * pad, h + 2 * pad]; set();
    }
    bar.addEventListener('click', function (e) {
      var a = e.target.dataset && e.target.dataset.a;
      if (a === 'in') zoom(0.7); else if (a === 'out') zoom(1 / 0.7);
      else if (a === 'fit') { vb = vb0.slice(); set(); }
      else if (a === 'full') {
        var host = box.parentNode;
        if (document.fullscreenElement) document.exitFullscreen();
        else if (host.requestFullscreen) host.requestFullscreen();
      } else if (e.target.dataset && e.target.dataset.sec) {
        var g = svg.querySelector('#' + CSS.escape(e.target.dataset.sec));
        if (g) {  // Graphviz draws inside a translated group: measure on screen and convert to view coordinates
          var r = g.getBoundingClientRect();
          var a = toSvg({clientX: r.left, clientY: r.top}), z = toSvg({clientX: r.right, clientY: r.bottom});
          fitTo(a[0], a[1], z[0] - a[0], z[1] - a[1]);
        }
      }
    });
    document.addEventListener('fullscreenchange', function () {
      svg.style.height = document.fullscreenElement ? 'calc(100vh - 3.5em)' : natural();
    });

    // --- wheel, drag, pinch ---------------------------------------------------------------------------------
    svg.addEventListener('wheel', function (e) {
      e.preventDefault();
      var p = toSvg(e);
      zoom(e.deltaY < 0 ? 0.85 : 1 / 0.85, p[0], p[1]);
    }, {passive: false});
    var drag = null, moved = false, pts = {};
    svg.addEventListener('pointerdown', function (e) {
      pts[e.pointerId] = e;
      drag = {x: e.clientX, y: e.clientY, vb: vb.slice(), s: toSvg(e)[2]}; moved = false;
      svg.style.cursor = 'grabbing';
    });
    window.addEventListener('pointermove', function (e) {
      if (!drag) return;
      var ids = Object.keys(pts);
      if (ids.length === 2 && pts[e.pointerId]) {  // pinch
        var o = pts[ids[0] == e.pointerId ? ids[1] : ids[0]];
        var d0 = Math.hypot(pts[e.pointerId].clientX - o.clientX, pts[e.pointerId].clientY - o.clientY);
        var d1 = Math.hypot(e.clientX - o.clientX, e.clientY - o.clientY);
        pts[e.pointerId] = e;
        if (d0 > 0 && d1 > 0) { var p = toSvg(e); zoom(d0 / d1, p[0], p[1]); }
        moved = true; return;
      }
      var dx = e.clientX - drag.x, dy = e.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 3) moved = true;
      vb = [drag.vb[0] - dx * drag.s, drag.vb[1] - dy * drag.s, vb[2], vb[3]]; set();
    });
    window.addEventListener('pointerup', function (e) {
      delete pts[e.pointerId];
      if (!Object.keys(pts).length) { drag = null; svg.style.cursor = 'grab'; }
    });
    svg.addEventListener('click', function (e) { if (moved) { e.preventDefault(); e.stopPropagation(); } }, true);

    // --- sections: one button per cluster -------------------------------------------------------------------
    var secs = bar.querySelector('.mz-secs');
    svg.querySelectorAll('g.cluster').forEach(function (g, i) {
      if (!g.id) g.id = 'mz-cluster-' + i;
      var t = g.querySelector('text');
      var name = t ? t.textContent.trim() : ('section ' + (i + 1));
      var b = document.createElement('button'); b.textContent = name; b.dataset.sec = g.id; b.title = 'zoom to ' + name;
      secs.appendChild(b);
    });

    // a link «mapa.html#sec=3» opens the map zoomed on the third section
    var hs = /sec=(\d+)/.exec(location.hash);
    if (hs) { var bt = secs.querySelectorAll('button')[Number(hs[1]) - 1]; if (bt) bt.click(); }

    // --- dependency highlight -------------------------------------------------------------------------------
    var nodes = {}, edges = [];
    svg.querySelectorAll('g.node').forEach(function (g) {
      var t = g.querySelector('title'); if (t) nodes[t.textContent.trim()] = g;
    });
    svg.querySelectorAll('g.edge').forEach(function (g) {
      var t = g.querySelector('title'); if (!t) return;
      var m = t.textContent.split('->'); if (m.length === 2) edges.push({a: m[0].trim(), b: m[1].trim(), g: g});
    });
    function light(id) {
      var keep = {}; keep[id] = 1;
      edges.forEach(function (e) {
        var on = e.a === id || e.b === id;
        e.g.classList.toggle('mz-dim', !on); e.g.classList.toggle('mz-on', on);
        if (on) { keep[e.a] = 1; keep[e.b] = 1; }
      });
      Object.keys(nodes).forEach(function (k) { nodes[k].classList.toggle('mz-dim', !keep[k]); });
    }
    function clear() {
      edges.forEach(function (e) { e.g.classList.remove('mz-dim', 'mz-on'); });
      Object.keys(nodes).forEach(function (k) { nodes[k].classList.remove('mz-dim'); });
    }
    Object.keys(nodes).forEach(function (k) {
      nodes[k].addEventListener('mouseenter', function () { if (!drag) light(k); });
      nodes[k].addEventListener('mouseleave', clear);
    });
  }

  var css = document.createElement('style');
  css.textContent = '.mz-bar{display:flex;flex-wrap:wrap;gap:.3em;align-items:center;margin:.4em 0;font:13px Arial,sans-serif}' +
    '.mz-bar button,.mz-bar a{font:13px Arial,sans-serif;border:1px solid #9fb7cf;background:#fff;border-radius:4px;' +
    'padding:.15em .6em;cursor:pointer;color:#222;text-decoration:none}.mz-bar button:hover,.mz-bar a:hover{background:#e3edf7}' +
    '.mz-help{color:#666;font-size:12px;margin:0 .4em}.mz-secs{display:flex;flex-wrap:wrap;gap:.3em;width:100%}' +
    '.mz-phone{font-size:13px;color:#456;background:#eef4fa;border:1px solid #c9d6e3;border-radius:6px;' +
    'padding:.3em .6em;margin:.3em 0}@media (max-width:700px){.mz-help{display:none}}' +
    '.mz-secs button{font-size:12px;background:#f5f8fc}' +
    'g.mz-dim{opacity:.12;transition:opacity .15s}g.edge.mz-on path{stroke-width:2.2}g.edge.mz-on polygon{stroke-width:2}' +
    'g.edge.lm-aux{opacity:.18}g.edge.lm-aux.mz-on{opacity:1}' +
    ':fullscreen{background:#fff;padding:.6em;overflow:auto}';
  document.head.appendChild(css);
  function all() { document.querySelectorAll('div.mapa').forEach(init); }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', all); else all();
  // the map in the overview sits in a <details>: initialise it when it is opened (getBBox needs it visible)
  document.addEventListener('toggle', function (e) { if (e.target.open) all(); }, true);
})();
