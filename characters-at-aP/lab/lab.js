// lab.js — laboratorio del Teorema A.  La pagina se pinta sin esperar: Pyodide (Python en el navegador) se carga
// DESPUES, en segundo plano (requestIdleCallback / setTimeout), y el boton se activa cuando esta listo.
// Calculos: evlib.py del suplemento (el mismo fichero), via lab_A.py.  El reloj se dibuja aqui en SVG.
(function () {
  var PYODIDE = 'https://cdn.jsdelivr.net/pyodide/v0.27.2/full/';
  var py = null, estado = null;

  function $(id) { return document.getElementById(id); }
  function pon(txt, cls) { if (estado) { estado.textContent = txt; estado.className = 'labestado ' + (cls || ''); } }

  function cargaScript(src) {
    return new Promise(function (ok, mal) {
      var s = document.createElement('script'); s.src = src; s.async = true;
      s.onload = ok; s.onerror = function () { mal(new Error('no se pudo cargar ' + src)); };
      document.head.appendChild(s);
    });
  }

  async function arranca() {
    try {
      pon('⏳ loading Python in the background (first time ~20 s)…', 'carga');
      await cargaScript(PYODIDE + 'pyodide.js');
      py = await loadPyodide({ indexURL: PYODIDE });
      pon('⏳ loading numpy, mpmath, sympy…', 'carga');
      await py.loadPackage(['numpy', 'mpmath', 'sympy']);
      for (var f of ['evlib.py', 'lab_A.py']) {
        var r = await fetch('lab/' + f); if (!r.ok) throw new Error('falta ' + f);
        py.FS.writeFile(f, await r.text());
      }
      py.runPython('import sys; sys.path.insert(0, "."); import lab_A');
      pon('✅ Python ready — exact arithmetic in Z[ζ_q], same code as the supplement (evlib.py)', 'listo');
      $('labboton').disabled = false;
      calcula();
    } catch (e) { pon('❌ could not load Python: ' + e.message, 'error'); }
  }

  // semaforo por clase: verde = queda sitio, ambar = llena justo, rojo = se desborda (=> caracter 0)
  function semaforo(f) {
    var n = f.l.length;
    if (n > f.cap) return { c: 'rojo', e: '🔴', t: 'overflow', col: '#d32f2f' };
    if (n === f.cap && n > 0) return { c: 'ambar', e: '🟡', t: 'full', col: '#f9a825' };
    return { c: 'verde', e: '🟢', t: 'room left', col: '#2e7d32' };
  }

  function reloj(res) {
    var q = res.q, W = 260, R = 95, cx = 130, cy = 125, svg = [];
    svg.push('<svg width="' + W + '" height="250" viewBox="0 0 ' + W + ' 250" xmlns="http://www.w3.org/2000/svg">');
    svg.push('<circle cx="' + cx + '" cy="' + cy + '" r="' + R + '" fill="none" stroke="#aaa"/>');
    var pal = ['#e07a5f', '#3d85c6', '#6aa84f', '#b4a7d6', '#f1c232', '#76a5af', '#c27ba0', '#93c47d', '#e69138', '#8e7cc3'];
    function clase(c) { return Math.min(((c % q) + q) % q, ((-c % q) + q) % q); }
    var luzDe = {};
    res.filas.forEach(function (f) { luzDe[f.clase] = semaforo(f); });
    for (var c = 0; c < q; c++) {
      var a = Math.PI / 2 - 2 * Math.PI * c / q, x = cx + R * Math.cos(a), y = cy - R * Math.sin(a);
      var luz = luzDe[clase(c)];
      svg.push('<circle cx="' + x + '" cy="' + y + '" r="11" fill="' + pal[clase(c) % pal.length] + '" opacity="0.35" stroke="' +
               (luz ? luz.col : '#999') + '" stroke-width="3"/>');
      svg.push('<text x="' + (cx + 1.22 * R * Math.cos(a)) + '" y="' + (cy - 1.22 * R * Math.sin(a) + 4) + '" font-size="11" text-anchor="middle" fill="#333">' + c + '</text>');
    }
    var usados = {};
    res.ell.forEach(function (l) {
      var c = l % q, n = usados[c] || 0; usados[c] = n + 1;
      var a = Math.PI / 2 - 2 * Math.PI * c / q, r = R * (0.78 - 0.17 * n), x = cx + r * Math.cos(a), y = cy - r * Math.sin(a);
      svg.push('<circle cx="' + x + '" cy="' + y + '" r="6" fill="' + pal[clase(c) % pal.length] + '" stroke="#000"/>');
      svg.push('<text x="' + (x + 8) + '" y="' + (y + 4) + '" font-size="10">' + l + '</text>');
    });
    svg.push('</svg>'); return svg.join('');
  }

  // «See the computation»: se despliega solo cuando el usuario cambia algo; si lo pliega a mano, se respeta.
  var verCalculo = false;
  function calculaUsuario() { verCalculo = true; calcula(); }

  function calcula() {
    if (!py) return;
    actualizaEnlace();
    var m = $('labm').value, k = $('labk').value, lam = $('lablam').value;
    var res = JSON.parse(py.globals.get('lab_A').lab(parseInt(m), parseInt(k), lam));
    var out = $('labsalida');
    if (res.error) { out.innerHTML = '<p class="laberror">⚠️ ' + res.error + '</p>'; return; }
    var desb = res.filas.some(function (f) { return f.l.length > f.cap; });
    var tabla = res.filas.map(function (f) {
      var nom = f.fija ? '{' + f.clase + '}' : '{' + f.clase + ',' + (res.q - f.clase) + '}';
      var luz = semaforo(f);
      return '<tr class="sem-' + luz.c + '"><td>' + nom + (f.fija ? ' (fixed)' : '') + '</td><td>' + f.l.join(', ') +
             '</td><td>' + f.l.length + ' / ' + f.cap + '</td><td>' + luz.e + ' ' + luz.t + '</td></tr>';
    }).join('');
    var titular;
    var pastilla = res.chi === 0 ? '<span class="pastilla rojo">🔴 χ = 0 · a class overflows</span>'
                                 : '<span class="pastilla verde">🟢 χ ≠ 0 · every class fits</span>';
    if (!res.acuerdo) titular = '<p class="labtitular mal">❌ Theorem A and the exact character disagree here — please report it.</p>';
    else if (res.chi === 0) {
      var c0 = res.filas.filter(function (f) { return f.l.length > f.cap; })[0];
      titular = '<p class="labtitular ok">✅ Theorem A is right: the character is <b>0</b>, because the numbers ' +
                c0.l.join(' and ') + ' crowd into the same class (room for only ' + c0.cap + ').</p>';
    } else titular = '<p class="labtitular ok">✅ Theorem A is right: the character is <b>' + res.chi +
                     '</b>, exactly as its formula predicts.</p>';
    out.innerHTML = '<p>' + pastilla + ' <button type="button" id="labenlace" title="Copy a link that opens this exact example">🔗 Share this example</button></p>' +
      titular + '<details class="labdetalle"' + (verCalculo ? ' open' : '') + '><summary>🔎 See the computation, step by step</summary>' +
      '<div class="labgrid"><div>' + reloj(res) + '</div><div>' +
      '<p>Sp(' + 2 * res.m + '), a<sub>P</sub><sup>' + res.k + '</sup> = g<sub>' + res.p + '/' + res.q + '</sub> &nbsp; (t = ' + res.t + ', d = ' + res.d + ', q = ' + res.q + ')</p>' +
      '<p>λ = (' + res.lam.join(', ') + ') &nbsp; ℓ = λ+ρ = (' + res.ell.join(', ') + ')</p>' +
      '<table class="labtabla"><tr><th>class</th><th>ℓ<sub>i</sub> in it</th><th>count / capacity</th><th></th></tr>' + tabla + '</table>' +
      '<p>N<sub>q</sub>(ℓ) = ' + res.Nq_ell + ', N<sub>q</sub>(ρ) = ' + res.Nq_rho + ' → Theorem A predicts ' + (desb ? '<b>χ = 0</b>' : '<b>χ ≠ 0</b>') + '</p>' +
      '<p>🧮 Theorem A formula: <b>' + res.formula + '</b> &nbsp;&nbsp; 🔬 exact character: <b>' + res.chi + '</b></p>' +
      '<p class="' + (res.acuerdo ? 'labok' : 'labmal') + '">' + (res.acuerdo ? '✅ they agree' : '❌ they disagree — please report this') + '</p>' +
      '</div></div>' + lectura(res, desb) + '</details>';
    ultimoInforme = informe(res, desb);
    var det = out.querySelector('details.labdetalle');
    if (det) det.addEventListener('toggle', function () { verCalculo = det.open; });
  }

  // ---- enlace para compartir: #lab=m,k,l1-l2-... abre exactamente este ejemplo ----
  function actualizaEnlace() {
    var lam = $('lablam').value.split(/[ ,;]+/).filter(Boolean).join('-');
    var h = '#lab=' + $('labm').value + ',' + $('labk').value + ',' + lam;
    try { history.replaceState(null, '', h); } catch (e) {}
  }
  function leeEnlace() {
    var m = /#lab=(\d+),(\d+),([\d-]+)/.exec(location.hash);
    return m ? { m: parseInt(m[1]), k: parseInt(m[2]), lam: m[3].split('-').map(Number) } : null;
  }
  document.addEventListener('click', function (e) {
    if (e.target && e.target.id === 'labenlace') {
      var b = e.target, url = location.href;
      var hecho = function () { b.textContent = '✅ Link copied'; setTimeout(function () { b.textContent = '🔗 Share this example'; }, 1500); };
      try { navigator.clipboard.writeText(url).then(hecho, function () { b.textContent = url; }); }
      catch (err) { b.textContent = url; }
    }
  });

  // ---- lectura en palabras del resultado, para valorarlo ----
  var ultimoInforme = '';
  function nombreClase(res, f) { return f.fija ? '{' + f.clase + '}' : '{' + f.clase + ',' + (res.q - f.clase) + '}'; }
  function lineas(res, desb) {
    var L = [];
    L.push('Setting: Sp(' + 2 * res.m + '), power k = ' + res.k + ' of Kostant\'s element (t = 2m+2 = ' + res.t +
           '), so d = gcd(k,t) = ' + res.d + ', q = t/d = ' + res.q + ', p = k/d = ' + res.p + '.');
    L.push('Weight: λ = (' + res.lam.join(', ') + '), ℓ = λ + ρ = (' + res.ell.join(', ') + '), ρ = (' + res.rho.join(', ') + ').');
    var over = res.filas.filter(function (f) { return f.l.length > f.cap; });
    if (desb) {
      over.forEach(function (f) {
        L.push('Class ' + nombreClase(res, f) + (f.fija ? ' (fixed)' : '') + ' holds ' + f.l.join(' and ') + ': ' +
               f.l.length + ' numbers, but its capacity is ' + f.cap + ' — it overflows.');
      });
      L.push('So N_q(ℓ) = ' + res.Nq_ell + ' > N_q(ρ) = ' + res.Nq_rho + ', and Theorem A(1) predicts χ = 0.');
    } else {
      L.push('Every class is within its capacity, so N_q(ℓ) = N_q(ρ) = ' + res.Nq_rho + ' and Theorem A(1) predicts χ ≠ 0.');
      var fl = res.div_l.map(function (x) { return x[0] + ' → ' + x[1]; }).join(', ') || 'none';
      var fr = res.div_r.map(function (x) { return x[0] + ' → ' + x[1]; }).join(', ') || 'none';
      L.push('Root values divisible by q = ' + res.q + ' at ℓ: ' + fl + '; product Z_q(ℓ) = ' + res.Zl + '.');
      L.push('Root values divisible by q at ρ: ' + fr + '; product Z_q(ρ) = ' + res.Zr + '.');
      L.push('Sign: E_{p,q}(λ) = ' + res.E + ', so (−1)^E = ' + (res.E % 2 ? '−1' : '+1') + '.');
      L.push('Theorem A(2): χ = (−1)^E · Z_q(ℓ)/Z_q(ρ) = ' + (res.E % 2 ? '−' : '+') + res.Zl + '/' + res.Zr + ' = ' + res.formula + '.');
    }
    L.push('Independent check: the exact character in Z[ζ_q] (evlib.chi_ps) is ' + res.chi + '.');
    if (res.chi !== 0 && res.factores && res.factores.length) {
      var partes = res.factores.map(function (f) {
        var g = f.tipo === 'Sp' ? 'Sp(' + 2 * f.n + ')' : f.tipo === 'SO' ? 'SO(' + (2 * f.n + 1) + ')' : 'GL(' + f.n + ')';
        return g + ' with ν = (' + f.nu.join(', ') + '), dimension ' + f.dim;
      });
      L.push('Theorem B: one factor per class — ' + partes.join('; ') + '. κ = ' + res.kappa + ', so |χ| = ' + res.kappa +
             ' × ' + res.factores.map(function (f) { return f.dim; }).join(' × ') + ' = ' + res.kappa * res.Delta +
             (res.acuerdoB ? ' ✅ (matches the exact character)' : ' ❌ (does not match)') + '.');
    }
    L.push(res.acuerdo ? 'Verdict: the prediction of Theorem A is confirmed in this case.'
                       : 'Verdict: MISMATCH between Theorem A and the exact character — please report it.');
    return L;
  }
  function lectura(res, desb) {
    return '<div class="lablectura"><p><b>📝 Reading of the result</b> ' +
           '<button type="button" id="labcopia">📋 Copy report</button></p><ol>' +
           lineas(res, desb).map(function (x) { return '<li>' + x + '</li>'; }).join('') + '</ol></div>';
  }
  function informe(res, desb) {
    return ['Theorem A lab — characters of Sp(2m) at powers of Kostant\'s element', ''].concat(
      lineas(res, desb).map(function (x, i) { return (i + 1) + '. ' + x; }),
      ['', 'Computed with evlib.py (supplementary material), exact arithmetic.']).join('\n');
  }
  document.addEventListener('click', function (e) {
    if (e.target && e.target.id === 'labcopia') {
      var b = e.target;
      var hecho = function () { b.textContent = '✅ Copied'; setTimeout(function () { b.textContent = '📋 Copy report'; }, 1500); };
      try { navigator.clipboard.writeText(ultimoInforme).then(hecho, function () { window.prompt('Copy the report:', ultimoInforme); }); }
      catch (err) { window.prompt('Copy the report:', ultimoInforme); }
    }
  });

  function inicia() {
    estado = $('labestado'); if (!estado) return;
    // menus: m de 2 a 8; k solo con los valores validos 1..2m+1, mostrando q
    var selm = $('labm'), selk = $('labk');
    for (var mm = 2; mm <= 8; mm++) selm.add(new Option('m = ' + mm + '  (Sp(' + 2 * mm + '))', mm));
    function gcd(a, b) { while (b) { var r = a % b; a = b; b = r; } return a; }
    function rellenaK(kSel) {
      var m = parseInt(selm.value), t = 2 * m + 2; selk.innerHTML = '';
      for (var k = 1; k < t; k++) selk.add(new Option('k = ' + k + '  (q = ' + t / gcd(k, t) + ')', k));
      selk.value = Math.min(kSel || 2, t - 1);
    }
    function ponLam(arr) { $('lablam').value = arr.join(', '); }
    function ejemplo(m, k, lam) { selm.value = m; rellenaK(k); ponLam(lam); calculaUsuario(); }
    var compartido = leeEnlace();   // si la URL trae #lab=..., se abren esos parametros en la vista Explore, con el calculo desplegado
    if (compartido) {
      selm.value = Math.min(8, Math.max(2, compartido.m)); rellenaK(compartido.k); ponLam(compartido.lam); verCalculo = true;
      var vb = document.querySelector('#vistas button[data-v=explore]'); if (vb) vb.click();
      var bl = estado.closest('details'); if (bl) { bl.open = true; setTimeout(function () { bl.scrollIntoView(); }, 300); }
    } else { selm.value = 4; rellenaK(2); }
    var espera = null;
    var auto = function () { clearTimeout(espera); espera = setTimeout(calculaUsuario, 350); };
    selm.addEventListener('change', function () { rellenaK(parseInt(selk.value)); calculaUsuario(); });
    selk.addEventListener('change', calculaUsuario);
    $('lablam').addEventListener('input', auto);
    $('labboton').addEventListener('click', calculaUsuario);
    $('labej1').addEventListener('click', function () { ejemplo(4, 2, [1, 1, 0, 0]); });
    $('labej2').addEventListener('click', function () { ejemplo(4, 2, [6, 2, 0, 0]); });
    $('labej3').addEventListener('click', function () {
      var m = 2 + Math.floor(Math.random() * 5), t = 2 * m + 2, k = 1 + Math.floor(Math.random() * (t - 1));
      var lam = [], top = Math.floor(Math.random() * 7);
      for (var i = 0; i < m; i++) { top = Math.floor(Math.random() * (top + 1)); lam.push(top); }
      lam.sort(function (a, b) { return b - a; });
      ejemplo(m, k, lam);
    });
    // Python solo se carga si el laboratorio llega a verse (vista Explore y bloque abierto): un lector en la vista
    // Paper no descarga nada.  La carga ocurre despues de pintar la pagina, en segundo plano.
    var lanzado = false;
    var lanzar = function () {
      if (lanzado) return; lanzado = true;
      var go = function () { arranca(); };
      if ('requestIdleCallback' in window) requestIdleCallback(go, { timeout: 2000 }); else setTimeout(go, 500);
    };
    if ('IntersectionObserver' in window) {
      var obs = new IntersectionObserver(function (es) {
        es.forEach(function (e) { if (e.isIntersecting) { lanzar(); obs.disconnect(); } });
      });
      obs.observe(estado);
    } else { lanzar(); }
    // y tambien por eventos explicitos: vista Explore con el lab abierto, o abrir el bloque del lab
    var bloque = estado.closest('details');
    var visible = function () { return !document.body.classList.contains('vista-paper') && (!bloque || bloque.open); };
    document.addEventListener('vista', function () { if (visible()) lanzar(); });
    if (bloque) bloque.addEventListener('toggle', function () { if (visible()) lanzar(); });
    if (visible()) lanzar();
    pon('⏳ Python will load when you open this lab (once, in the background)…', 'carga');
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', inicia); else inicia();
})();
