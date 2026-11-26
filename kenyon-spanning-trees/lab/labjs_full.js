// encaje: asset de Lemmario (excovery.lemmario, labjs.py): la ventana central de los labs JavaScript (engine = 'js'),
// la misma que da lab.js a los labs Pyodide (mismas clases y aspecto); no es una herramienta aparte.
/* The central window for every JavaScript lab of the page (labjs.py puts this script before the labs' own scripts).

25-nov (Carles, dyck-divisors: «iba bien porque no había que desplazarse con la barra lateral»): the Pyodide labs of
lab.js had a «⛶ full screen» button, an optional fixed button on the page ([[lab]] button = '…') and the central
window (.lm-full): controls on the left, figures on the right, ✕ and Esc to close and come back to the same place, the
page darkened behind; on a phone (max-width 760px) one column that scrolls, with the ✕ fixed. A JavaScript lab is a
box .lm-jslab around the lab's own fragment; this script gives each box the same.

Which part goes to the right: the element of the fragment marked class="lm-figs" (or data-lm-figs), the first one;
everything else, in its order, goes to the left. A fragment with no such mark opens in one column. Opening and closing
send the page a «resize» event and the box a «lm-lab-resize» event (detail.full = true/false), after the new layout:
a lab that draws at the width of its container redraws there.
A page without .lm-jslab boxes: nothing is added. */
(function () {
  'use strict';
  var CSS =
    '.lm-full-btn{padding:.2em .8em;cursor:pointer;border:1px solid #1B6F8C;background:#eef5f9;border-radius:14px;font-weight:bold;color:#1B4F63}' +
    'body.lm-noscroll{overflow:hidden}' +
    'body.lm-noscroll::before{content:"";position:fixed;inset:0;background:rgba(20,30,40,.45);z-index:99998}' +
    '.lm-central-btn{position:fixed;right:18px;top:62px;z-index:9000;padding:.55em 1.1em;font:bold 14px Arial,sans-serif;' +
    'color:#fff;background:#1B6F8C;border:none;border-radius:22px;box-shadow:0 3px 10px rgba(0,0,0,.25);cursor:pointer}' +
    '.lm-central-btn:hover{background:#155a72}' +
    '.lm-x{position:absolute;top:8px;right:10px;z-index:2;width:34px;height:34px;border-radius:50%;border:1px solid #c5ced8;' +
    'background:#fff;font:bold 18px Arial,sans-serif;line-height:30px;cursor:pointer;color:#455A64;box-shadow:0 1px 4px rgba(0,0,0,.15)}' +
    '.lm-x:hover{background:#f3d6d6;color:#b71c1c}' +
    // the window: as .lm-full of lab.js (fixed, 2.5% margins, rounded, shadow); here the window scrolls as a whole and
    // the figures stay in view (sticky), because a JS lab's left part is not one block that could scroll by itself
    '.lm-jslab.lm-full{position:fixed;inset:2.5vh 2.5vw;z-index:99999;background:#fff;color:#222;margin:0;padding:.8em 1em;' +
    'box-sizing:border-box;overflow-y:auto;overflow-x:hidden;border-radius:10px;box-shadow:0 10px 40px rgba(0,0,0,.35)}' +
    '.lm-jslab.lm-full.lm-full-2col{display:grid;grid-template-columns:minmax(330px,36%) 1fr;gap:0 1.2em;align-content:start}' +
    '.lm-jslab.lm-full .lm-fflat{display:contents}' +
    '.lm-jslab.lm-full .lm-fleft{min-width:0;font-size:13px;line-height:1.45}' +
    '.lm-jslab.lm-full .lm-fleft.lm-form,.lm-jslab.lm-full .lm-fleft .lm-form{display:grid;grid-template-columns:1fr 1fr;gap:.35em .6em;align-items:end}' +
    '.lm-jslab.lm-full .lm-form label{display:flex;flex-direction:column;font-size:12px}' +
    '.lm-jslab.lm-full .lm-form input,.lm-jslab.lm-full .lm-form select{width:100%;max-width:none;box-sizing:border-box}' +
    '.lm-jslab.lm-full .lm-fleft.lm-ex{font-size:12px}' +
    '.lm-jslab.lm-full .lm-fright{min-width:0;position:sticky;top:0;align-self:start;max-height:calc(95vh - 1.6em);overflow:auto;' +
    'border-left:1px solid #e3e8ee;padding-left:1em;padding-right:38px;box-sizing:border-box}' +  // room for the ✕
    '.lm-jslab.lm-full .lm-fright svg{max-width:100%;height:auto}' +
    '@media (max-width:760px){' +
    '.lm-jslab.lm-full,.lm-jslab.lm-full.lm-full-2col{inset:0;border-radius:0;display:block;overflow-y:auto;overflow-x:hidden;' +
    '-webkit-overflow-scrolling:touch;padding:3em .7em 1.5em}' +
    '.lm-jslab.lm-full .lm-fright{position:static;max-height:none;overflow:visible;border-left:0;padding:0;margin:.6em 0}' +
    '.lm-jslab.lm-full>.lm-x{position:fixed;top:8px;right:8px;width:40px;height:40px;z-index:100000}' +
    '.lm-central-btn{right:10px;top:auto;bottom:14px;font-size:13px;padding:.5em .9em}}';

  var SKIP = {SCRIPT: 1, STYLE: 1, NOSCRIPT: 1, TEMPLATE: 1};

  function figsOf(box) {
    var all = box.querySelectorAll('.lm-figs, [data-lm-figs]');
    return all.length ? all[0] : null;
  }

  function mount(box) {
    if (box.getAttribute('data-lm-full') === 'on') return;  // once per box
    box.setAttribute('data-lm-full', 'on');
    var fb = document.createElement('button');
    fb.type = 'button'; fb.className = 'lm-full-btn'; fb.textContent = '⛶ full screen';
    fb.title = 'the lab on the whole screen: controls left, figures right (Esc closes it)';
    var form = box.querySelector('.lm-form'), st = form && form.querySelector('.lm-state');
    if (st) form.insertBefore(fb, st); else if (form) form.appendChild(fb); else box.insertBefore(fb, box.firstChild);

    var placed = [], saved = null, opened = [], view = null;

    function layout(on) {
      placed.forEach(function (el) {
        el.classList.remove('lm-fflat', 'lm-fleft', 'lm-fright');
        el.style.gridColumn = ''; el.style.gridRow = '';
      });
      placed = [];
      box.classList.remove('lm-full-2col');
      box.style.gridTemplateRows = '';
      var figs = on && figsOf(box);
      if (!figs) return;
      var flat = [];
      for (var e = figs.parentElement; e && e !== box; e = e.parentElement) flat.push(e);
      var items = [];
      (function collect(parent) {
        for (var i = 0; i < parent.children.length; i++) {
          var c = parent.children[i];
          if (flat.indexOf(c) >= 0) { c.classList.add('lm-fflat'); placed.push(c); collect(c); }
          else if (c !== figs && !SKIP[c.tagName] && !c.classList.contains('lm-x')) items.push(c);
        }
      })(box);
      items.forEach(function (c, i) {
        c.classList.add('lm-fleft'); c.style.gridColumn = '1'; c.style.gridRow = String(i + 1); placed.push(c);
      });
      figs.classList.add('lm-fright'); figs.style.gridColumn = '2'; figs.style.gridRow = '1 / span ' + (items.length + 1);
      placed.push(figs);
      // the last row takes the rest: the figures (which span it) never stretch the rows of the controls
      box.style.gridTemplateRows = 'repeat(' + items.length + ', auto) 1fr';
      box.classList.add('lm-full-2col');
    }

    function redraw(on) {
      var send = function () {
        try { window.dispatchEvent(new Event('resize')); } catch (e) {}
        try { box.dispatchEvent(new CustomEvent('lm-lab-resize', {bubbles: true, detail: {full: on}})); } catch (e) {}
      };
      if (window.requestAnimationFrame) requestAnimationFrame(function () { requestAnimationFrame(send); }); else setTimeout(send, 30);
    }

    function full(on) {
      if (on === box.classList.contains('lm-full')) return;
      if (on) {
        // the page may scroll in a pane (classic layout), not in the window: remember every scrolled ancestor too
        saved = [window.pageXOffset, window.pageYOffset, []];
        for (var a = box.parentElement; a; a = a.parentElement) if (a.scrollTop || a.scrollLeft) saved[2].push([a, a.scrollLeft, a.scrollTop]);
        opened = []; view = null;
        // the lab may sit in a closed block (details) or in a view that hides it (Paper / Explore)
        for (var d = box.parentElement; d; d = d.parentElement) if (d.tagName === 'DETAILS' && !d.open) { d.open = true; opened.push(d); }
        if (box.offsetParent === null) {
          var sw = document.querySelector('button[data-v="explore"]'), back = document.querySelector('button[data-v="paper"]');
          if (sw) { sw.click(); view = back; }
        }
      }
      box.classList.toggle('lm-full', on);
      layout(on);
      // 31-oct (lab.js, Carles: «que la ventana se pueda cerrar x»): a ✕ in the window's top-right corner
      var x = box.querySelector(':scope > .lm-x');
      if (on && !x) {
        x = document.createElement('button');
        x.type = 'button'; x.className = 'lm-x'; x.textContent = '✕'; x.title = 'close (Esc)';
        x.addEventListener('click', function () { full(false); });
        box.appendChild(x);
      } else if (!on && x) x.parentNode.removeChild(x);
      document.body.classList.toggle('lm-noscroll', on);
      fb.textContent = on ? '✕ close (Esc)' : '⛶ full screen';
      if (on) box.scrollTop = 0;
      else {  // back where the reader was
        opened.forEach(function (d) { d.open = false; });
        if (view) view.click();
        if (saved) {
          window.scrollTo(saved[0], saved[1]);
          saved[2].forEach(function (s) { s[0].scrollLeft = s[1]; s[0].scrollTop = s[2]; });
        }
      }
      redraw(on);
    }
    box.__lmFull = full;

    fb.addEventListener('click', function () { full(!box.classList.contains('lm-full')); });
    document.addEventListener('keydown', function (e) { if (e.key === 'Escape' && box.classList.contains('lm-full')) full(false); });
    var label = box.getAttribute('data-lm-button');
    if (label) {  // a fixed button on the page: the lab in the central window, wherever the reader is
      var cb = document.createElement('button');
      cb.type = 'button'; cb.className = 'lm-central-btn'; cb.textContent = label;
      cb.title = 'open the lab in the central window (Esc closes it and leaves you where you were)';
      cb.addEventListener('click', function () { full(true); });
      document.body.appendChild(cb);
    }
  }

  function all() {
    var boxes = document.querySelectorAll('.lm-jslab');
    if (!boxes.length) return;
    if (!document.getElementById('lm-jslab-full-css')) {
      var css = document.createElement('style');
      css.id = 'lm-jslab-full-css'; css.textContent = CSS;
      document.head.appendChild(css);
    }
    for (var i = 0; i < boxes.length; i++) mount(boxes[i]);
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', all); else all();
})();
