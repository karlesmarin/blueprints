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
      if (lab.figure_live === false) {  // the figure stays static; only a button to the lab, where it is drawn live
        if (img.parentElement.querySelector(':scope > .lm-figlink[data-lab="' + lab.id + '"]')) return;
        var go = document.createElement('button');
        go.type = 'button'; go.className = 'lm-figlink'; go.setAttribute('data-lab', lab.id);
        go.textContent = '🧪 ' + (lab.figure_link || 'Your own input: the lab') + ' →';
        go.addEventListener('click', function () { open(); });
        img.insertAdjacentElement('afterend', go);
        return;
      }
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
    // {kind: 'svg', svg, title}: a drawing composed by the lab's own Python (any figure of the paper, redrawn live)
    if (p.kind === 'svg') return '<div class="lm-svg">' + (p.title ? '<p class="lm-svgtitle">' + esc(p.title) + '</p>' : '') +
      String(p.svg).replace(/<script[\s\S]*?<\/script>/gi, '') + '</div>';
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
      // 27-oct (Carles: «le damos herramientas para que prueben»): type 'textarea' takes the reader's own data (one
      // item per line), so a lab can run on a whole list (their qubits, their pulse samples), not only on our values
      if (inp.type === 'textarea') {
        form += '<label class="lm-ta">' + esc(inp.label || inp.name) + '<br><textarea data-name="' + inp.name + '" rows="' +
          (inp.rows || 5) + '" cols="' + (inp.size || 60) + '" spellcheck="false">' + esc(inp['default']) + '</textarea></label> ';
        return;
      }
      var a = inp.type === 'int' ? ' type="number" min="' + (inp.min !== undefined ? inp.min : '') + '" max="' + (inp.max !== undefined ? inp.max : '') + '"' : ' type="text" size="' + (inp.size || 18) + '"';
      form += '<label>' + esc(inp.label || inp.name) + ' <input data-name="' + inp.name + '"' + a + ' value="' + esc(inp['default']) + '"></label> ';
    });
    form += '<button type="button" class="lm-run" disabled>Compute</button>' +
      (lab.random ? ' <button type="button" class="lm-dice" title="random inputs: see what happens">🎲 random</button>' : '') +
      ' <span class="lm-state">⏳ Python loads when you open this lab</span></div>';
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
      box.querySelectorAll('[data-name]').forEach(function (i) { v[i.dataset.name] = i.value; });
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
        // 27-oct (Carles: «que pueda dar un resumen del resultado»): the live figure carries the lab's summary under it
        placed.filter(function (f, i) { return placed.indexOf(f) === i; }).forEach(function (f) {
          var s = slotOf(f);
          if (!s) return;
          var sum = s.querySelector(':scope > .lm-figsum');
          if (!res.text) { if (sum) sum.remove(); return; }
          if (!sum) { sum = document.createElement('p'); sum.className = 'lm-figsum'; s.appendChild(sum); }
          sum.innerHTML = '🧾 ' + res.text;
          if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([sum]).catch(function () {});
        });
        if (placed.length) {
          h += '<p class="lm-placed">🖼 The paper\'s figure shows these values, in its place: <button type="button" ' +
            'class="lm-goto" data-fig="' + esc(placed[0]) + '">go to the figure ↑</button></p>';
        }
        // the reader takes the result away: the table as CSV, and a link that reopens the lab with these inputs
        h += '<p class="lm-tools">' + (res.table ? '<button type="button" class="lm-csv">⬇ table as CSV</button> ' : '') +
          '<button type="button" class="lm-link">🔗 copy a link with these values</button> <span class="lm-toolmsg"></span></p>';
        out.innerHTML = h;
        var msg = out.querySelector('.lm-toolmsg'), csvb = out.querySelector('.lm-csv');
        if (csvb) csvb.addEventListener('click', function () {
          var q = function (x) { x = String(x); return /[",\n]/.test(x) ? '"' + x.replace(/"/g, '""') + '"' : x; };
          var text = [res.table.head].concat(res.table.rows).map(function (r) { return r.map(q).join(','); }).join('\n');
          var a = document.createElement('a');
          a.href = URL.createObjectURL(new Blob([text + '\n'], {type: 'text/csv'}));
          a.download = (lab['function'] || 'lab') + '.csv';
          document.body.appendChild(a); a.click(); a.remove();
        });
        out.querySelector('.lm-link').addEventListener('click', function () {
          var url = location.origin + location.pathname + '?' + new URLSearchParams(Object.assign({lab: lab.node}, values())) + '#' + lab.node;
          var shown = function () { msg.innerHTML = '<input type="text" readonly size="40" value="' + esc(url) + '">'; msg.querySelector('input').select(); };
          if (navigator.clipboard) navigator.clipboard.writeText(url).then(function () { msg.textContent = '✓ copied'; }, shown); else shown();
        });
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
    // 29-oct (Carles: «un dado para variables aleatorias»): the lab's own random_inputs() picks valid random inputs
    function dice() {
      if (!py) { start(); return; }
      try {
        // «module.function» names a dice in another file of the lab (30-oct, qsl-diagnostics: one dice module for
        // several labs); a bare name is looked up in the lab's own module
        var dot = lab.random.lastIndexOf('.');
        var rmod = dot > 0 ? lab.random.slice(0, dot) : lab.module, rfun = dot > 0 ? lab.random.slice(dot + 1) : lab.random;
        var r = JSON.parse(py.globals.get('__import__')(rmod)[rfun]());
        Object.keys(r).forEach(function (k) { var i = box.querySelector('[data-name="' + k + '"]'); if (i) i.value = r[k]; });
        document.querySelectorAll('.lm-figform[data-lab="' + lab.id + '"] input[data-mirror]').forEach(function (m) {
          var i = box.querySelector('[data-name="' + m.dataset.mirror + '"]'); if (i) m.value = i.value;
        });
        compute();
      } catch (e) { out.innerHTML = '<p class="lm-err">⚠️ ' + esc(e.message) + '</p>'; }
    }
    var db = box.querySelector('.lm-dice');
    if (db) db.addEventListener('click', dice);
    box.querySelectorAll('[data-name]').forEach(function (i) {
      i.addEventListener('change', compute);
      i.addEventListener('keydown', function (e) { if (e.key === 'Enter' && i.tagName !== 'TEXTAREA') compute(); });
    });
    box.querySelectorAll('[data-ex]').forEach(function (b) {
      b.addEventListener('click', function () {
        var e = lab.examples[Number(b.dataset.ex)];
        Object.keys(e).forEach(function (k) {
          var i = box.querySelector('[data-name="' + k + '"]'); if (i) i.value = e[k];
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
        var i = box.querySelector('[data-name="' + inp.name + '"]');
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
    // 21-oct (Carles: «los parámetros dinámicos tendrían que estar al lado de las figuras»): each live figure carries
    // the lab's inputs and examples too, in sync with the lab's own form (either one recomputes both)
    (lab.figures || []).forEach(function (name) {
      var slot = slotOf(name);
      if (!slot || slot.parentElement.querySelector(':scope > .lm-figform[data-lab="' + lab.id + '"]')) return;
      var bar = document.createElement('div');
      bar.className = 'lm-form lm-figform'; bar.setAttribute('data-lab', lab.id);
      bar.innerHTML = lab.inputs.filter(function (inp) { return inp.type !== 'textarea'; }).map(function (inp) {
        var a = inp.type === 'int' ? ' type="number" min="' + (inp.min !== undefined ? inp.min : '') + '" max="' + (inp.max !== undefined ? inp.max : '') + '"' : ' type="text" size="' + (inp.size || 18) + '"';
        return '<label>' + esc(inp.label || inp.name) + ' <input data-mirror="' + inp.name + '"' + a + ' value="' + esc(inp['default']) + '"></label>';
      }).join(' ') + (lab.random ? ' <button type="button" class="lm-figex lm-figdice" title="random inputs">🎲 random</button>' : '') +
      (lab.examples || []).map(function (e, i) {
        return ' <button type="button" class="lm-figex" data-ex="' + i + '">' + esc(e.label || Object.values(e).join(', ')) + '</button>';
      }).join('');
      slot.insertAdjacentElement('beforebegin', bar);
      function go() { if (py && started) compute(); else start(); }
      var fd = bar.querySelector('.lm-figdice');
      if (fd) fd.addEventListener('click', function () { if (py && started) dice(); else start(); });
      bar.querySelectorAll('input[data-mirror]').forEach(function (m) {
        function push() { var i = box.querySelector('input[data-name="' + m.dataset.mirror + '"]'); if (i) i.value = m.value; go(); }
        m.addEventListener('change', push); m.addEventListener('keydown', function (e) { if (e.key === 'Enter') push(); });
      });
      bar.querySelectorAll('[data-ex]').forEach(function (b) {
        b.addEventListener('click', function () {
          var e = lab.examples[Number(b.dataset.ex)];
          Object.keys(e).forEach(function (k) { var i = box.querySelector('[data-name="' + k + '"]'); if (i) i.value = e[k]; });
          go();
        });
      });
    });
    // the lab's form → the figures' bars (a value typed in one place shows in the other)
    var mirror = function () {
      document.querySelectorAll('.lm-figform[data-lab="' + lab.id + '"] input[data-mirror]').forEach(function (m) {
        var i = box.querySelector('input[data-name="' + m.dataset.mirror + '"]'); if (i) m.value = i.value;
      });
    };
    run.addEventListener('click', mirror);
    box.querySelectorAll('[data-name]').forEach(function (i) { i.addEventListener('change', mirror); });
    box.querySelectorAll('[data-ex]').forEach(function (b) { b.addEventListener('click', mirror); });
    document.querySelectorAll('.lm-figform[data-lab="' + lab.id + '"] [data-ex]').forEach(function (b) { b.addEventListener('click', mirror); });
    if (linked) open();
  }

  var css = document.createElement('style');
  css.textContent = '.lm-form{display:flex;flex-wrap:wrap;gap:.6em;align-items:center;margin:.4em 0}.lm-form input{padding:.15em .3em}' +
    '.lm-run,.lm-ex button,.lm-dice{padding:.2em .8em;cursor:pointer;border:1px solid #ef6c00;background:#fff;border-radius:14px}' +
    '.lm-dice,.lm-figdice{background:#fff3e0!important;font-weight:bold}' +
    '.lm-ex{margin:.3em 0}.lm-state{font-size:.9em;color:#555}.lm-err{color:#c62828}' +
    '.lm-tab{border-collapse:collapse;font-size:.9em;margin:.4em 0}.lm-tab td,.lm-tab th{border:1px solid #ddd;padding:.15em .5em}' +
    '.lm-out svg{margin:.4em 0;display:block}' +
    '.lm-figform{justify-content:center;font:13px Arial,sans-serif;background:#fff8f0;border:1px solid #f3d3b0;border-radius:10px;padding:.3em .6em}' +
    '.lm-figex{padding:.15em .7em;cursor:pointer;border:1px solid #ef6c00;background:#fff;border-radius:14px;font:12px Arial,sans-serif}' +
    '.lm-ta{display:block;width:100%}.lm-ta textarea{width:100%;box-sizing:border-box;font:12px/1.4 monospace}' +
    '.lm-tools button{font:12px Arial,sans-serif;padding:.15em .7em;border:1px solid #8a9aab;background:#fff;border-radius:12px;cursor:pointer}' +
    '.lm-figslot>div{margin:.3em 0}.lm-figsum{font:13px/1.45 Arial,sans-serif;background:#f6f9fb;border-left:3px solid #1B6F8C;padding:.4em .7em;margin:.4em 0;border-radius:4px}' +
    '.lm-figwait{font:13px Arial,sans-serif;color:#8a4a00}' +
    '.lm-figtoggle{display:block;margin:.3em auto;padding:.15em .8em;cursor:pointer;border:1px solid #8a9aab;background:#fff;border-radius:14px;font:12px Arial,sans-serif}' +
    '.lm-placed{font-size:.92em;color:#555}.lm-goto{cursor:pointer;border:1px solid #8a9aab;background:#fff;border-radius:14px;padding:.05em .7em}' +
    '.lm-figlink{display:block;margin:.4em auto;padding:.25em 1em;cursor:pointer;border:1px solid #ef6c00;background:#fff8f0;border-radius:14px;font:13px Arial,sans-serif;color:#8a4a00}';
  document.head.appendChild(css);
  function all() { (window.LEMMARIO_LABS || []).forEach(function (l) { setup(l, window.LEMMARIO_LABS); }); }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', all); else all();
})();
