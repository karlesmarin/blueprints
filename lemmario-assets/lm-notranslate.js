
(function(){
  var SEL = 'mjx-container,code,pre,.lean_decl,.MathJax,svg,canvas';
  function mark(root) {
    (root || document).querySelectorAll(SEL).forEach(function (e) {
      if (e.getAttribute('translate') !== 'no') { e.setAttribute('translate', 'no'); e.classList.add('notranslate'); }
    });
  }
  function start() {
    mark();
    if (window.MathJax && MathJax.startup && MathJax.startup.promise) MathJax.startup.promise.then(function () { mark(); });
    // 24-nov: solo los nodos AÑADIDOS y fuera de las figuras 3D (.l3). Antes, cada cambio volvía a recorrer el
    // documento entero en cada fotograma; con una figura 3D que gira sola (lab3d) era un bucle sin fin: Chrome sin
    // ventana no terminaba nunca la página de dilogarithm-clock y en el navegador gastaba CPU sin parar.
    new MutationObserver(function (records) {
      records.forEach(function (r) {
        r.addedNodes.forEach(function (n) {
          if (n.nodeType !== 1 || (n.closest && n.closest('.l3'))) return;
          if (n.matches && n.matches(SEL) && n.getAttribute('translate') !== 'no') {
            n.setAttribute('translate', 'no'); n.classList.add('notranslate');
          }
          mark(n);
        });
      });
    }).observe(document.body, {childList: true, subtree: true});
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
