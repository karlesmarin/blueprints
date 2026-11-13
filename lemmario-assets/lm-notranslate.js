
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
    var due = null;  // a lab or MathJax adds nodes: mark them, at most once per animation frame
    new MutationObserver(function () {
      if (due === null) due = requestAnimationFrame(function () { due = null; mark(); });
    }).observe(document.body, {childList: true, subtree: true});
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
