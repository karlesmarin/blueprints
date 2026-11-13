
(function(){
  var n = new URLSearchParams(location.search).get('n');
  if (!n) return;
  function go(){
    var a = null;
    document.querySelectorAll('svg a').forEach(function (x) {
      var h = x.getAttribute('href') || x.getAttribute('xlink:href') || '';
      if (!a && h.slice(h.indexOf('#') + 1) === n) a = x;
    });
    var g = a && (a.closest('g.node') || a.parentNode);
    if (!g) return;
    var pane = g.closest('section.pc-pane');
    g.classList.add('lm-here');
    var name = (a.getAttribute('xlink:title') || a.getAttribute('title') || n).split(':')[0];
    var bar = document.getElementById('lm-herebar');
    if (!bar) {
      bar = document.createElement('div'); bar.id = 'lm-herebar';
      var host = (pane || document.body);
      host.insertBefore(bar, host.firstChild);
    }
    bar.innerHTML = '📍 <b></b> on the map · <a href="index.html#' + encodeURIComponent(n) + '">← back to the statement</a>';
    bar.querySelector('b').textContent = name;
    setTimeout(function () { g.scrollIntoView({block: 'center', inline: 'center'}); }, 300);
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', go); else go();
  window.addEventListener('load', go);
})();
