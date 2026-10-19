/* Lemmario: interactive labs. Each lab runs its own Python file in the browser (Pyodide, loaded only when a lab is
   opened) and shows what it returns: {text, table: {head, rows}, plot: {title, xlabel, ylabel, step, x, series: [{name,
   y}]}, plots: [...], error}; a plot with a kind is drawn by its module (lab3d.js, lablevels.js). Configuration: window.LEMMARIO_LABS = [{id, files, module, function, packages, inputs, examples}]. */
(function () {
  var PYODIDE = 'https://cdn.jsdelivr.net/pyodide/v0.27.2/full/';
  var py = null, loading = null;
  var COLORS = ['#c2185b', '#1565c0', '#2e7d32', '#ef6c00', '#6a1b9a', '#00838f'];

  function load(src) {
    return new Promise(function (ok, bad) {
      var s = document.createElement('script'); s.src = src; s.onload = ok;
      s.onerror = function () { bad(new Error('cannot load ' + src)); }; document.head.appendChild(s);
    });
  }
  function ready(labs) {
    if (!loading) loading = (async function () {
      await load(PYODIDE + 'pyodide.js');
      py = await loadPyodide({indexURL: PYODIDE});
      var pk = [], files = [], inline = {};
      labs.forEach(function (l) {
        pk = pk.concat(l.packages || []); files = files.concat(l.files); Object.assign(inline, l.sources || {});
      });
      if (pk.length) await py.loadPackage(pk);
      for (var f of files) {
        var name = f.split('/').pop(), text = inline[name];
        if (text === undefined) {  // older pages: fetch the file (works over http only)
          var r = await fetch('lab/' + f); if (!r.ok) throw new Error('missing lab/' + f);
          text = await r.text();
        }
        py.FS.writeFile(name, text);
      }
      py.runPython('import sys; sys.path.insert(0, ".")');
      return py;
    })();
    return loading;
  }
  function esc(s) { return String(s).replace(/[&<>]/g, function (c) { return {'&': '&amp;', '<': '&lt;', '>': '&gt;'}[c]; }); }

  function plot(p) {
    var W = 560, H = 300, L = 52, R = 14, T = 26, B = 42;
    var xs = p.x, all = [];
    p.series.forEach(function (s) { all = all.concat(s.y.filter(function (v) { return v !== null; })); });
    var xmin = Math.min.apply(null, xs), xmax = Math.max.apply(null, xs);
    var ymin = Math.min(0, Math.min.apply(null, all)), ymax = Math.max.apply(null, all);
    if (ymax === ymin) ymax = ymin + 1; if (xmax === xmin) xmax = xmin + 1;
    function X(v) { return L + (v - xmin) / (xmax - xmin) * (W - L - R); }
    function Y(v) { return H - B - (v - ymin) / (ymax - ymin) * (H - T - B); }
    var o = ['<svg viewBox="0 0 ' + W + ' ' + H + '" style="max-width:100%;background:#fff;border:1px solid #dde3ea;border-radius:6px" xmlns="http://www.w3.org/2000/svg">'];
    o.push('<text x="' + (W / 2) + '" y="16" text-anchor="middle" font-size="13">' + esc(p.title || '') + '</text>');
    var ny = 5;
    for (var i = 0; i <= ny; i++) {
      var v = ymin + (ymax - ymin) * i / ny, y = Y(v);
      o.push('<line x1="' + L + '" x2="' + (W - R) + '" y1="' + y + '" y2="' + y + '" stroke="#eee"/>');
      o.push('<text x="' + (L - 6) + '" y="' + (y + 4) + '" text-anchor="end" font-size="11">' + (Math.round(v * 100) / 100) + '</text>');
    }
    xs.forEach(function (v) {
      o.push('<text x="' + X(v) + '" y="' + (H - B + 16) + '" text-anchor="middle" font-size="11">' + v + '</text>');
    });
    o.push('<text x="' + (W / 2) + '" y="' + (H - 6) + '" text-anchor="middle" font-size="12">' + esc(p.xlabel || '') + '</text>');
    o.push('<text x="14" y="' + (H / 2) + '" text-anchor="middle" font-size="12" transform="rotate(-90 14 ' + (H / 2) + ')">' + esc(p.ylabel || '') + '</text>');
    p.series.forEach(function (s, k) {
      var c = s.color || COLORS[k % COLORS.length], d = '', prev = null;
      xs.forEach(function (x, i) {
        var y = s.y[i]; if (y === null || y === undefined) { prev = null; return; }
        if (prev === null) d += 'M' + X(x) + ' ' + Y(y);
        else if (p.step) d += 'H' + X(x) + 'V' + Y(y);
        else d += 'L' + X(x) + ' ' + Y(y);
        prev = y;
      });
      o.push('<path d="' + d + '" fill="none" stroke="' + c + '" stroke-width="2.2"' + (s.dash ? ' stroke-dasharray="6 4"' : '') + '/>');
      xs.forEach(function (x, i) {
        if (s.y[i] !== null && s.y[i] !== undefined) o.push('<circle cx="' + X(x) + '" cy="' + Y(s.y[i]) + '" r="3" fill="' + c + '"/>');
      });
      o.push('<rect x="' + (L + 10) + '" y="' + (T + 6 + 16 * k) + '" width="12" height="3" fill="' + c + '"/>');
      o.push('<text x="' + (L + 28) + '" y="' + (T + 10 + 16 * k) + '" font-size="11">' + esc(s.name) + '</text>');
    });
    o.push('</svg>');
    return o.join('');
  }

  function table(t) {
    var h = '<table class="lm-tab"><tr>' + t.head.map(function (x) { return '<th>' + esc(x) + '</th>'; }).join('') + '</tr>';
    t.rows.forEach(function (r) { h += '<tr>' + r.map(function (x) { return '<td>' + esc(x) + '</td>'; }).join('') + '</tr>'; });
    return h + '</table>';
  }

  // a lab that redraws figures of the paper (lemmario.toml: figures = ['fig_3_arco_exacto']) takes their place
  // (Carles, 19-oct: «quita la fig y pon esto»): when the reader reaches the figure the lab runs with its default
  // inputs and its plots that name the figure ({figure, panel}) replace the image, which stays one click away (and
  // shows meanwhile, or if Python cannot load). The lab's own inputs then redraw the figure in place, not twice.
  function slotOf(name) {
    var img = document.querySelector('img[alt*="' + name + '"]');
    return img ? img.parentElement.querySelector(':scope > .lm-figslot[data-for="' + name + '"]') : null;
  }
  function figureSlots(lab, open, start) {
    (lab.figures || []).forEach(function (name) {
      var img = document.querySelector('img[alt*="' + name + '"]');
      if (!img || slotOf(name)) return;
      var slot = document.createElement('div'), tg = document.createElement('button'), a = document.createElement('button');
      slot.className = 'lm-figslot'; slot.setAttribute('data-for', name);
      slot.innerHTML = '<div class="lm-figwait">⏳ the live figure loads here (Python in the browser, first time ~15 s)…</div>';
      tg.type = 'button'; tg.className = 'lm-figtoggle'; tg.hidden = true; tg.textContent = '📄 show the paper\'s static figure';
      tg.addEventListener('click', function () {
        var hide = img.style.display !== 'none';
        img.style.display = hide ? 'none' : '';
        tg.textContent = hide ? '📄 show the paper\'s static figure' : '📄 hide the paper\'s static figure';
      });
      a.type = 'button'; a.className = 'lm-figlink';
      a.textContent = '🧪 ' + (lab.figure_link || 'Your own input: the lab') + ' →';
      a.addEventListener('click', function () { open(); });
      img.insertAdjacentElement('beforebegin', slot);
      img.insertAdjacentElement('afterend', a);
      img.insertAdjacentElement('afterend', tg);
      if ('IntersectionObserver' in window) {
        var io = new IntersectionObserver(function (es) {
          if (es.some(function (e) { return e.isIntersecting; })) { io.disconnect(); start(); }
        }, {rootMargin: '300px'});
        io.observe(img);
      }
    });
  }
  // a plot naming a figure goes to that figure's slot (its panel in its own block, panels in order); false if the page
  // has no such figure (then the lab shows it itself)
  function place(p) {
    var slot = slotOf(p.figure);
    if (!slot) return false;
    var w = slot.querySelector('.lm-figwait');
    if (w) w.remove();
    var key = p.panel || '', box = slot.querySelector(':scope > [data-panel="' + key + '"]');
    if (!box) {
      box = document.createElement('div'); box.setAttribute('data-panel', key);
      var after = [].filter.call(slot.children, function (c) { return c.getAttribute('data-panel') < key; });
      if (after.length) after[after.length - 1].insertAdjacentElement('afterend', box); else slot.prepend(box);
    }
    box.innerHTML = figure(p);
    mount3d(box);
    var img = slot.parentElement.querySelector('img[alt*="' + p.figure + '"]'), tg = slot.parentElement.querySelector(':scope > .lm-figtoggle');
    if (tg && tg.hidden) { tg.hidden = false; img.style.display = 'none'; }  // first time: the live figure replaces the image
    return true;
  }

  // a plain plot is SVG text; a figure of another kind ({kind: '3d'} in lab3d.js, {kind: 'levels'} in lablevels.js…)
  // is a live element: a slot now, mounted by its module (window.LemmarioFigures[kind]) once in the page
  var pending = [];
  function figure(p) {
    if (!p.kind) return plot(p);
    pending.push(p);
    return '<div class="lm-3d" data-3d="' + (pending.length - 1) + '"></div>';
  }
  function mount3d(root) {
    root.querySelectorAll('.lm-3d[data-3d]').forEach(function (el) {
      var i = Number(el.getAttribute('data-3d')), p = pending[i];
      pending[i] = null;  // mounted: the figure keeps its data, the list need not
      el.removeAttribute('data-3d');
      var kind = (window.LemmarioFigures || {})[p.kind];
      if (kind) kind.mount(el, p);
      else el.innerHTML = '<p class="lm-err">⚠️ no module draws figures of kind ' + esc(p.kind) + '</p>';
    });
  }

  function setup(lab, labs) {
    var box = document.querySelector('[data-lemmario-lab="' + lab.id + '"]');
    if (!box) return;
    var form = '<div class="lm-form">';
    lab.inputs.forEach(function (inp) {
      var a = inp.type === 'int' ? ' type="number" min="' + (inp.min !== undefined ? inp.min : '') + '" max="' + (inp.max !== undefined ? inp.max : '') + '"' : ' type="text" size="' + (inp.size || 18) + '"';
      form += '<label>' + esc(inp.label || inp.name) + ' <input data-name="' + inp.name + '"' + a + ' value="' + esc(inp['default']) + '"></label> ';
    });
    form += '<button type="button" class="lm-run" disabled>Compute</button> <span class="lm-state">⏳ Python loads when you open this lab</span></div>';
    if (lab.examples && lab.examples.length) {
      form += '<div class="lm-ex">Examples: ' + lab.examples.map(function (e, i) {
        return '<button type="button" data-ex="' + i + '">' + esc(e.label || Object.values(e).join(', ')) + '</button>';
      }).join(' ') + '</div>';
    }
    form += '<div class="lm-out"></div>';
    box.innerHTML = form;
    var state = box.querySelector('.lm-state'), run = box.querySelector('.lm-run'), out = box.querySelector('.lm-out');
    function values() {
      var v = {};
      box.querySelectorAll('input[data-name]').forEach(function (i) { v[i.dataset.name] = i.value; });
      return v;
    }
    function compute() {
      if (!py) { start(); return; }  // a click before Python is ready: load it, then compute (start() computes)
      try {
        var f = py.globals.get('__import__')(lab.module)[lab['function']];
        var res = JSON.parse(f(JSON.stringify(values())));
        if (res.error) { out.innerHTML = '<p class="lm-err">⚠️ ' + esc(res.error) + '</p>'; return; }
        var h = '';
        if (res.text) h += '<p>' + res.text + '</p>';
        if (res.table) h += table(res.table);
        var placed = [];
        [].concat(res.plot || [], res.plots || []).forEach(function (p) {
          if (p.figure && place(p)) placed.push(p.figure); else h += figure(p);
        });
        if (placed.length) {
          h += '<p class="lm-placed">🖼 The paper\'s figure shows these values, in its place: <button type="button" ' +
            'class="lm-goto" data-fig="' + esc(placed[0]) + '">go to the figure ↑</button></p>';
        }
        out.innerHTML = h;
        var go = out.querySelector('.lm-goto');
        if (go) go.addEventListener('click', function () {
          var paper = document.querySelector('button[data-v="paper"]'), s = slotOf(go.getAttribute('data-fig'));
          if (s && s.offsetParent === null && paper) paper.click();  // the figure may live in the other view
          if (s) s.scrollIntoView({block: 'start'});
        });
        mount3d(out);
        if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([out]).catch(function () {});  // \( … \) in a text
        if (scrollOnce) { scrollOnce = false; target().scrollIntoView({block: 'start'}); }  // a linked lab: show it
      } catch (e) { out.innerHTML = '<p class="lm-err">⚠️ ' + esc(e.message) + '</p>'; }
    }
    run.addEventListener('click', compute);
    box.querySelectorAll('input[data-name]').forEach(function (i) {
      i.addEventListener('change', compute); i.addEventListener('keydown', function (e) { if (e.key === 'Enter') compute(); });
    });
    box.querySelectorAll('[data-ex]').forEach(function (b) {
      b.addEventListener('click', function () {
        var e = lab.examples[Number(b.dataset.ex)];
        Object.keys(e).forEach(function (k) {
          var i = box.querySelector('input[data-name="' + k + '"]'); if (i) i.value = e[k];
        });
        compute();
      });
    });
    var started = false;
    function start() {  // once per lab: Python itself is shared by all the labs of the page (ready() loads it once)
      if (started) return;
      started = true;
      state.textContent = '⏳ loading Python in the browser (first time ~15 s)…';
      ready(labs).then(function () { state.textContent = '✅ Python ready'; run.disabled = false; compute(); })
        .catch(function (e) { state.textContent = '❌ ' + e.message; });
    }
    // a link can open this lab with its inputs set: index.html?lab=<node>&<input>=<value>…#<node> (e.g. from a paper)
    var P = new URLSearchParams(location.search), linked = P.get('lab') === lab.node, scrollOnce = linked, blk = null;
    if (linked) {
      lab.inputs.forEach(function (inp) {
        var i = box.querySelector('input[data-name="' + inp.name + '"]');
        if (i && P.has(inp.name)) i.value = P.get(inp.name);
      });
    }
    var det = box.closest('details');
    if (det) det.addEventListener('toggle', function () { if (det.open) start(); });
    else start();
    // show this lab: from a link (?lab=…), or from the button under a figure of the paper it redraws. A link with
    // fig=<image name> (from the paper's caption) goes on to that figure, drawn live, instead of the lab's form
    var toFig = linked && (lab.figures || []).indexOf(P.get('fig')) >= 0 ? P.get('fig') : null;
    function target() {
      var s = toFig && slotOf(toFig);
      if (s && !s.querySelector('.lm-figwait')) return s.closest('details') || s;
      return blk || box;
    }
    function open() {
      // the labs live in the «Explore» view: switch to it if the page is on another one
      // (the «Paper» view hides the lab blocks with a class on the document, and a pane may be hidden too)
      blk = box.closest('details') || box;
      // and a one-page site shows one part at a time (classic.py): the statement's hash opens the part that holds it
      if (lab.node && decodeURIComponent(location.hash.slice(1)) !== lab.node) location.hash = lab.node;
      var sw = document.querySelector('button[data-v="explore"]');
      if (sw && (box.offsetParent === null || getComputedStyle(blk).display === 'none')) sw.click();
      for (var d = box.parentElement; d; d = d.parentElement) if (d.tagName === 'DETAILS') d.open = true;  // opens → start()
      var fs = toFig && slotOf(toFig);  // the figure's own block (a closed «Figure» block hides the live figure)
      for (d = fs && fs.parentElement; d; d = d.parentElement) if (d.tagName === 'DETAILS') d.open = true;
      if (!det) start();
      if (started && py) { target().scrollIntoView({block: 'start'}); return; }  // already computed: just go there
      scrollOnce = true;  // and again when the result is shown (compute): the page may have jumped elsewhere meanwhile
      setTimeout(function () { target().scrollIntoView({block: 'start'}); }, linked ? 600 : 0);
    }
    figureSlots(lab, open, start);  // first: a link with fig= looks for the figure's slot
    if (linked) open();
  }

  var css = document.createElement('style');
  css.textContent = '.lm-form{display:flex;flex-wrap:wrap;gap:.6em;align-items:center;margin:.4em 0}.lm-form input{padding:.15em .3em}' +
    '.lm-run,.lm-ex button{padding:.2em .8em;cursor:pointer;border:1px solid #ef6c00;background:#fff;border-radius:14px}' +
    '.lm-ex{margin:.3em 0}.lm-state{font-size:.9em;color:#555}.lm-err{color:#c62828}' +
    '.lm-tab{border-collapse:collapse;font-size:.9em;margin:.4em 0}.lm-tab td,.lm-tab th{border:1px solid #ddd;padding:.15em .5em}' +
    '.lm-out svg{margin:.4em 0;display:block}' +
    '.lm-figslot>div{margin:.3em 0}.lm-figwait{font:13px Arial,sans-serif;color:#8a4a00}' +
    '.lm-figtoggle{display:block;margin:.3em auto;padding:.15em .8em;cursor:pointer;border:1px solid #8a9aab;background:#fff;border-radius:14px;font:12px Arial,sans-serif}' +
    '.lm-placed{font-size:.92em;color:#555}.lm-goto{cursor:pointer;border:1px solid #8a9aab;background:#fff;border-radius:14px;padding:.05em .7em}' +
    '.lm-figlink{display:block;margin:.4em auto;padding:.25em 1em;cursor:pointer;border:1px solid #ef6c00;background:#fff8f0;border-radius:14px;font:13px Arial,sans-serif;color:#8a4a00}';
  document.head.appendChild(css);
  function all() { (window.LEMMARIO_LABS || []).forEach(function (l) { setup(l, window.LEMMARIO_LABS); }); }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', all); else all();
})();
