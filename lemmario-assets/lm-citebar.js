
document.addEventListener('click', function (e) {
  var a = e.target.closest && e.target.closest('a.lm-cite');
  if (!a) return;
  e.preventDefault();
  var head = a.closest('[class$="_thmheading"]') || a.parentElement, box = head.nextElementSibling;
  if (box && box.classList.contains('lm-citebox')) { box.remove(); return; }
  box = document.createElement('div'); box.className = 'lm-citebox';
  box.textContent = a.getAttribute('data-cite');
  var b = document.createElement('button'); b.type = 'button'; b.textContent = 'copy';
  b.onclick = function () {
    try { navigator.clipboard.writeText(a.getAttribute('data-cite')); b.textContent = 'copied'; } catch (x) {}
  };
  box.appendChild(b);
  // the same statement in the blueprint's PDF, at its page (printpdf names a destination for every statement)
  var holder = head.closest('[id]');
  if (holder && document.querySelector('a.lm-dl[href="blueprint.pdf"]')) {
    var p = document.createElement('a');
    p.href = 'blueprint.pdf#nameddest=' + encodeURIComponent(holder.id); p.target = '_blank'; p.className = 'lm-inpdf';
    p.textContent = '📄 this statement in the blueprint PDF'; p.title = 'Open the blueprint PDF at this statement';
    box.appendChild(document.createElement('br')); box.appendChild(p);
  }
  head.insertAdjacentElement('afterend', box);
});
