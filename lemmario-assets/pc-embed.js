
(function(){
  if (window.self === window.top) return;
  document.documentElement.classList.add('pc-embed');
  function tell(){ try { window.parent.postMessage({pcLoc: location.href}, '*'); } catch (e) {} }
  window.addEventListener('hashchange', tell);
  window.addEventListener('load', tell);
  window.addEventListener('message', function(e){
    var d = e.data || {};
    if (d.pcVista) { var b = document.querySelector('#vistas button[data-v="' + d.pcVista + '"]'); if (b) b.click(); }
  });
})();
