
/* 21-oct, Carles: the Lean opens in a central window over the blueprint, and closing it leaves the reader where he was */
(function(){
  /* the browser's Back (or the phone's back gesture) closes the panel instead of leaving the blueprint: the panel
     pushes one history entry; closing it by hand takes that entry back out (21-oct: «que pueda volver donde estaba») */
  function quitar(){var p=document.querySelector('.lm-panel'),v=document.querySelector('.lm-veil');
    if(p)p.remove();if(v)v.remove();document.removeEventListener('keydown',esc);}
  function cerrar(){if(history.state&&history.state.lmPanel)history.back();else quitar();}
  window.addEventListener('popstate',function(){quitar();});
  function esc(e){if(e.key==='Escape')cerrar();}
  function abrir(href,nombre,gh){quitar();
    if(!(history.state&&history.state.lmPanel))history.pushState({lmPanel:1},'');
    var v=document.createElement('div');v.className='lm-veil';v.onclick=cerrar;
    var p=document.createElement('div');p.className='lm-panel';p.setAttribute('role','dialog');
    /* 21-oct, Carles: the window header has the name and Close only; the ✒️ stays in the Lean page's own header
       inside the window, as GitHub does (Carles: «está en dos sitios», «quita el emoji de esa leyenda») */
    p.innerHTML='<header><b></b>'+
      '<button type="button" title="Close (Esc)">✕ Close</button></header><iframe title="Lean source"></iframe>';
    p.querySelector('b').textContent=nombre||'';
    /* ?panel=1: the Lean page knows it is inside the window (no Atlas link) and the URL skips an old cached copy */
    var i=href.indexOf('#'),src=(i<0?href:href.slice(0,i))+'?panel=1'+(i<0?'':href.slice(i));
    p.querySelector('button').onclick=cerrar;p.querySelector('iframe').src=src;
    document.body.appendChild(v);document.body.appendChild(p);document.addEventListener('keydown',esc);}
  document.addEventListener('click',function(e){
    var a=e.target.closest&&e.target.closest('a[data-lean-github]');
    if(!a||e.ctrlKey||e.metaKey||e.shiftKey||e.button!==0)return;
    e.preventDefault();abrir(a.href,(a.textContent||'').trim(),a.getAttribute('data-lean-github'));},true);
})();
