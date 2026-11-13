
(function(){
  var opened = [], shown = [];
  addEventListener('beforeprint', function(){
    document.querySelectorAll('details:not([open]):not(.b-lab)').forEach(function(d){ d.open = true; opened.push(d); });
    document.querySelectorAll('img[style*="display: none"], img[style*="display:none"]').forEach(function(i){
      i.style.display = ''; shown.push(i); });
  });
  addEventListener('afterprint', function(){
    opened.forEach(function(d){ d.open = false; }); shown.forEach(function(i){ i.style.display = 'none'; });
    opened = []; shown = [];
  });
})();
