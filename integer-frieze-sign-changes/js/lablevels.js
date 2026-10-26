/* Lemmario: the «water level» figure of the labs, for counting parts that reach a level. A lab returns {kind:
   'levels', title, columns: [{name, short, parts: [n, ...], role: 'target' | 'allowed' | 'contrast'}], mark, bound,
   max, label}: each column is a matrix, each bar one of its parts (height n; null = ∞), and the water stands just
   below the level j the reader chooses: the bars that stick out are the parts ≥ j, and above each column their count
   ν_j. At the mark (the level of the proof) the target keeps more bars out of the water than any allowed matrix can
   (bound): the margin. Drag the slider or press ▶ (the water rises and stops at the mark). The names may carry TeX
   (\( … \)): MathJax typesets them when the page has it. With {panels: [spec, …], start_panel} it shows tabs, one
   panel at a time. Registered as window.LemmarioFigures.levels. */
(function () {
  var NS = 'http://www.w3.org/2000/svg';
  var ROLE = {target: '#CC79A7', allowed: '#E69F00', contrast: '#666666'};
  var REDUCED = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  function esc(s) { return String(s).replace(/[&<>]/g, function (c) { return {'&': '&amp;', '<': '&lt;', '>': '&gt;'}[c]; }); }
  function el(name, attrs, parent) {
    var e = document.createElementNS(NS, name);
    Object.keys(attrs).forEach(function (k) { e.setAttribute(k, attrs[k]); });
    if (parent) parent.appendChild(e);
    return e;
  }
  function count(parts, j) { return parts.filter(function (p) { return p === null || p >= j; }).length; }

  // several panels ({panels: [spec, …], start_panel}): tabs above, one panel drawn at a time
  function mount(host, spec) {
    if (!spec.panels) { draw(host, spec); return; }
    host.innerHTML = '<div class="lv-tabs">' + spec.panels.map(function (p, i) {
      return '<button type="button" data-i="' + i + '">' + esc(p.tab || p.title) + '</button>';
    }).join('') + '</div><div class="lv-panel"></div>';
    var inner = host.querySelector('.lv-panel'), tabs = host.querySelectorAll('.lv-tabs button');
    function pick(i) {
      tabs.forEach(function (b, m) { b.classList.toggle('on', m === i); });
      draw(inner, spec.panels[i]);
    }
    tabs.forEach(function (b, i) { b.addEventListener('click', function () { pick(i); }); });
    pick(spec.start_panel || 0);
  }

  function draw(host, spec) {
    var cols = spec.columns, top = spec.max + 1, W = 760, H = 380, L = 44, R = 16, T = 54, B = 46;
    var shown = cols.map(function (c) { return c.parts.filter(function (p) { return p === null || p > 0; }); });
    var nbars = shown.reduce(function (s, x) { return s + Math.max(1, x.length); }, 0);
    var gap = 26, bw = Math.max(5, Math.min(18, (W - L - R - gap * (cols.length - 1)) / nbars - 3));
    function Y(v) { return H - B - v / top * (H - T - B); }

    host.innerHTML = '<div class="lv"><div class="lv-title">' + esc(spec.title || '') + '</div><div class="lv-fig"></div>' +
      '<div class="lv-bar"><button type="button" class="lv-play" title="raise the water">▶</button>' +
      '<input type="range" min="1" max="' + spec.max + '" step="1"> <span class="lv-val"></span></div>' +
      '<div class="lv-legend"></div></div>';
    var svg = el('svg', {viewBox: '0 0 ' + W + ' ' + H, role: 'img', 'aria-label': spec.title || 'levels'}, host.querySelector('.lv-fig'));
    for (var v = 0; v <= spec.max; v += Math.max(1, Math.round(spec.max / 8))) {  // the level scale
      el('line', {x1: L, x2: W - R, y1: Y(v), y2: Y(v), stroke: '#eef1f4'}, svg);
      el('text', {x: L - 6, y: Y(v) + 4, 'text-anchor': 'end', 'font-size': 11, fill: '#555'}, svg).textContent = v;
    }
    el('text', {x: 13, y: (T + H - B) / 2, 'text-anchor': 'middle', 'font-size': 12, fill: '#333',
                transform: 'rotate(-90 13 ' + (T + H - B) / 2 + ')'}, svg).textContent = spec.label || 'level';
    if (spec.mark) {  // the level of the proof
      el('line', {x1: L, x2: W - R, y1: Y(spec.mark - 0.5), y2: Y(spec.mark - 0.5), stroke: '#333', 'stroke-dasharray': '2 4'}, svg);
      el('text', {x: W - R, y: Y(spec.mark - 0.5) - 4, 'text-anchor': 'end', 'font-size': 11, fill: '#333'}, svg)
        .textContent = 'level ' + spec.mark + ' (the proof)';
    }
    var bars = [], counts = [], x = L + 6;
    cols.forEach(function (c, i) {
      var col = ROLE[c.role] || '#555', w = Math.max(1, shown[i].length) * (bw + 3);
      shown[i].slice().sort(function (a, b) { return (b === null ? 1e9 : b) - (a === null ? 1e9 : a); }).forEach(function (p, m) {
        var h = p === null ? top : p;
        var r = el('rect', {x: x + m * (bw + 3), y: Y(h), width: bw, height: Y(0) - Y(h), rx: 2, fill: col}, svg);
        bars.push({r: r, p: p});
      });
      var cx = x + w / 2;
      counts.push({t: el('text', {x: cx, y: T - 22, 'text-anchor': 'middle', 'font-size': 15, 'font-weight': 'bold', fill: col}, svg),
                   c: c});
      el('text', {x: cx, y: H - B + 18, 'text-anchor': 'middle', 'font-size': 13, fill: col, 'font-weight': 'bold'}, svg)
        .textContent = c.short;
      var z = c.parts.length - shown[i].length;
      el('text', {x: cx, y: H - B + 33, 'text-anchor': 'middle', 'font-size': 10, fill: '#777'}, svg)
        .textContent = c.parts.length + ' parts' + (z ? ', ' + z + ' are 0' : '');
      x += w + gap;
    });
    // the water: in front of the bars, translucent, with a moving surface
    var water = el('rect', {x: L, width: W - L - R, fill: 'rgba(86,180,233,.28)'}, svg);
    var surf = el('path', {fill: 'none', stroke: '#2a8cc4', 'stroke-width': 2}, svg);
    var banner = el('text', {x: (L + W - R) / 2, y: 16, 'text-anchor': 'middle', 'font-size': 13, fill: '#333'}, svg);

    var range = host.querySelector('input'), val = host.querySelector('.lv-val'), play = host.querySelector('.lv-play');
    var j = spec.start || 1, level = j - 0.5, phase = 0, playing = false, hold = 0, last = 0;
    range.value = j;

    function paint() {
      var y = Y(level), d = '';
      for (var px = L; px <= W - R; px += 6) d += (px === L ? 'M' : 'L') + px + ' ' + (y + 2 * Math.sin(px / 18 + phase)).toFixed(1);
      water.setAttribute('y', y); water.setAttribute('height', Math.max(0, Y(0) - y));
      surf.setAttribute('d', d);
    }
    function show() {  // the counts for the level j (the water may still be moving towards it)
      val.textContent = (spec.level_name || 'level j') + ' = ' + j;
      bars.forEach(function (b) {
        var out = b.p === null || b.p >= j;
        b.r.setAttribute('opacity', out ? 1 : 0.28);
        b.r.setAttribute('stroke', out ? '#222' : 'none');
      });
      var tg = 0, al = 0;
      counts.forEach(function (k) {
        var n = count(k.c.parts, j);
        k.t.textContent = 'ν = ' + n;
        if (k.c.role === 'target') tg = Math.max(tg, n); else if (k.c.role === 'allowed') al = Math.max(al, n);
      });
      banner.textContent = j === spec.mark
        ? 'level ' + j + ': the target keeps ' + tg + ' parts out of the water, an allowed denominator at most ' +
          spec.bound + ' (here ' + al + ') — the margin'
        : 'parts ≥ ' + j + ' stick out of the water; ν counts them';
      banner.setAttribute('font-weight', j === spec.mark ? 'bold' : 'normal');
    }
    range.addEventListener('input', function () { j = Number(range.value); playing = false; play.textContent = '▶'; show(); });
    play.onclick = function () {
      playing = !playing; play.textContent = playing ? '⏸' : '▶';
      if (playing && j >= spec.max) { j = 1; level = 0.5; range.value = 1; show(); }
    };
    function tick(now) {
      if (!svg.isConnected) return;
      if (playing && now - last > (j === spec.mark ? 2200 : 700) && Math.abs(level - (j - 0.5)) < 0.02) {  // a pause at the mark
        last = now;
        if (j < spec.max) { j += 1; range.value = j; show(); } else { playing = false; play.textContent = '▶'; }
      }
      level += ((j - 0.5) - level) * 0.12;  // the water moves to its level, it does not jump
      if (!REDUCED) phase += 0.06;
      paint();
      requestAnimationFrame(tick);
    }
    var lg = host.querySelector('.lv-legend');
    lg.innerHTML = cols.map(function (c) {
      return '<div><b style="color:' + (ROLE[c.role] || '#555') + '">' + esc(c.short) + '</b> ' +
        (c.role === 'target' ? 'target ' : c.role === 'allowed' ? 'allowed: ' : 'contrast (not allowed): ') + c.name + '</div>';
    }).join('');
    if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([lg]).catch(function () {});
    show(); paint();
    requestAnimationFrame(tick);
  }

  var css = document.createElement('style');
  css.textContent = '.lv{margin:.5em 0;font:13px Arial,sans-serif}.lv-title{text-align:center;margin:.2em 0 .3em}' +
    '.lv-fig svg{display:block;width:100%;max-width:760px;background:#fff;border:1px solid #dde3ea;border-radius:6px}' +
    '.lv-fig rect{transition:opacity .35s}.lv-bar{display:flex;gap:.5em;align-items:center;margin:.35em 0}' +
    '.lv-bar button{padding:.1em .6em;cursor:pointer;border:1px solid #ef6c00;background:#fff;border-radius:14px}' +
    '.lv-bar input{flex:1;max-width:320px}.lv-legend{font-size:12.5px;line-height:1.6}' +
    '.lv-tabs{display:flex;flex-wrap:wrap;gap:.3em;margin:.3em 0}.lv-tabs button{padding:.15em .8em;cursor:pointer;' +
    'border:1px solid #CC79A7;background:#fff;border-radius:14px;font:12.5px Arial,sans-serif}' +
    '.lv-tabs button.on{background:#CC79A7;color:#fff}';
  document.head.appendChild(css);
  window.LemmarioFigures = window.LemmarioFigures || {};
  window.LemmarioFigures.levels = {mount: mount};
})();
