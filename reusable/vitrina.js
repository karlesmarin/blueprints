// Showcase of the reusable layer: copy buttons and the client-side search (statement words, area, Lean name).
(function () {
  function norm(s) {
    return (s || '').toLowerCase().normalize('NFD').replace(/[̀-ͯ]/g, '');
  }
  function copiar(texto, boton) {
    function hecho() {
      boton.textContent = 'copied';
      boton.classList.add('hecho');
      setTimeout(function () { boton.textContent = 'copy'; boton.classList.remove('hecho'); }, 1400);
    }
    if (navigator.clipboard && window.isSecureContext) {
      navigator.clipboard.writeText(texto).then(hecho, function () { viejo(texto); hecho(); });
    } else { viejo(texto); hecho(); }
  }
  function viejo(texto) {
    var t = document.createElement('textarea');
    t.value = texto; t.style.position = 'fixed'; t.style.opacity = '0';
    document.body.appendChild(t); t.select();
    try { document.execCommand('copy'); } catch (e) { /* nothing to do */ }
    document.body.removeChild(t);
  }
  document.addEventListener('click', function (ev) {
    var b = ev.target.closest('.copiar');
    if (!b) return;
    var texto = b.getAttribute('data-copiar');
    if (texto === null) {
      var caja = b.closest('.codigo'), c = caja && caja.querySelector('pre code');
      texto = c ? c.textContent : '';
    }
    copiar(texto, b);
  });

  var q = document.getElementById('q');
  if (!q) return;
  var tarjetas = Array.prototype.slice.call(document.querySelectorAll('.tarjeta'));
  var chips = Array.prototype.slice.call(document.querySelectorAll('.chip[data-area]'));
  var todas = document.getElementById('todas');  // "Show all": only visible while one area is selected
  var area = null;  // null = every area
  function elegir(a) {
    area = a;
    chips.forEach(function (d) { d.classList.toggle('on', area !== null && d.getAttribute('data-area') === area); });
    if (todas) todas.hidden = area === null;
    filtrar();
  }
  function filtrar() {
    var terms = norm(q.value).split(/\s+/).filter(Boolean), n = 0;
    tarjetas.forEach(function (t) {
      var txt = norm(t.getAttribute('data-q'));
      var ok = (area === null || t.getAttribute('data-area') === area) &&
        terms.every(function (w) { return txt.indexOf(w) >= 0; });
      t.hidden = !ok; if (ok) n++;
    });
    document.querySelectorAll('section.area').forEach(function (s) {
      s.hidden = !s.querySelector('.tarjeta:not([hidden])');
    });
    document.getElementById('nada').hidden = n > 0;
    document.getElementById('cuenta').textContent =
      (terms.length || area !== null) ? n + ' of ' + tarjetas.length + ' results' : '';
  }
  q.addEventListener('input', filtrar);
  chips.forEach(function (c) {
    c.addEventListener('click', function () {
      elegir(area === c.getAttribute('data-area') ? null : c.getAttribute('data-area'));
    });
  });
  if (todas) todas.addEventListener('click', function () { q.value = ''; elegir(null); });
  var h = new URLSearchParams(location.search).get('q');
  if (h) { q.value = h; }
  filtrar();
})();
