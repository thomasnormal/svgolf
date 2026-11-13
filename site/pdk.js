// svGolf site: the course selector (decided 2026-11-09: a dropdown on the front page; 2026-11-11/12: its courses are
// sky130 and ASAP7 placed and routed). Every page carries its golf scores twice, on sky130 (the default) and on the
// routed course, each in an element of class `pdk-sky130` or `pdk-asap7pnr` (site/build.py `dual`; both views computed
// when the site is built); style.css shows the one named by <html data-pdk>. This script:
//   * sets data-pdk before the page is drawn (it is loaded in <head>, not deferred): from the URL's ?pdk= first (a
//     link), else the reader's stored choice, else sky130. A page reached by Back or Forward takes the stored choice
//     first, since it is the reader's latest, and so does a page the browser restores from its back-forward cache;
//   * shows the selectors (the header's on every page but the front page and the 404 page; the front page's beside
//     its task cards), which change the view,
//     store the choice (localStorage, if the browser allows it: everything works without it) and put it in the URL;
//   * names the view in the URL of the page and in every link to the site's own pages (the charts' dots too, so a
//     link opened in a new tab or copied keeps it): ?pdk=asap7pnr, and ?pdk=sky130 once the reader has chosen a course
//     (a stored choice, a link that named one, a choice on this page), so that a copied link shows what its reader
//     saw. A reader who never chose keeps clean addresses; an address without ?pdk= shows each reader their own view.
//   * takes the old value, asap7 (the cells-only view the routed course replaced), from a link or a stored choice as
//     asap7pnr, and marks the page (<html data-pdk-moved>) so that its one-line notice says so: a reader never sees
//     another number under the old name without being told. The address and the stored choice then name asap7pnr.
// Without this script the page shows sky130 and says that the routed course needs it. No libraries, nothing fetched.
(function () {
  "use strict";

  var KEY = "svgolf-pdk";
  var DEFAULT = "sky130";
  var root = document.documentElement;

  var OLD = "asap7", ROUTED = "asap7pnr";   // the old value (ASAP7 cells only) and the course that replaced it
  var moved = false;                   // the view came from the old value (a link or a stored choice)

  // the two views, compared as strings (an object lookup would also accept "constructor", "toString", ...)
  function known(v) { return v === "sky130" || v === ROUTED; }

  // a value as this script takes it: the old one is the routed course, noted so that the notice says it
  function taken(v) {
    if (v === OLD) { moved = true; return ROUTED; }
    return known(v) ? v : null;
  }

  function fromUrl() {
    var m = /[?&]pdk=([^&#]*)/.exec(window.location.search || "");
    return taken(m ? m[1].toLowerCase() : null);     // ?pdk=ASAP7PNR is asap7pnr
  }

  function stored() {
    try {
      return taken(window.localStorage.getItem(KEY));
    } catch (e) {
      return null;                     // storage refused (a private window, file://, a policy): not remembered
    }
  }

  function store(v) {
    try { window.localStorage.setItem(KEY, v); } catch (e) { /* not remembered across pages: the URL carries it */ }
  }

  function cameBack() {                // the page was reached by Back or Forward
    try {
      var p = window.performance;
      var nav = p && p.getEntriesByType ? p.getEntriesByType("navigation")[0] : null;
      if (nav) { return nav.type === "back_forward"; }
      return !!(p && p.navigation && p.navigation.type === 2);
    } catch (e) {
      return false;
    }
  }

  var linked = fromUrl(), kept = stored();
  var current = (cameBack() ? kept || linked : linked || kept) || DEFAULT;
  var named = !!(linked || kept);      // the reader has chosen a library: the URL names it, sky130 included
  root.setAttribute("data-pdk", current);
  if (moved && current === ROUTED) { root.setAttribute("data-pdk-moved", ""); }
  if (linked && current === linked) { store(current); }   // a link's view goes on as its reader moves through the site
  else if (moved && kept === current) { store(current); }  // an old stored choice is kept under its new name

  // what ?pdk= says: the view, or nothing for a reader who never chose (the default, sky130)
  function param() { return named || current !== DEFAULT ? current : null; }

  // `href` with its pdk parameter set to `v` (removed for null), other parameters and the fragment kept
  function withPdk(href, v) {
    var hash = "", i = href.indexOf("#");
    if (i >= 0) { hash = href.slice(i); href = href.slice(0, i); }
    var query = "", j = href.indexOf("?");
    if (j >= 0) { query = href.slice(j + 1); href = href.slice(0, j); }
    var parts = query ? query.split("&").filter(function (p) { return p && p.split("=")[0] !== "pdk"; }) : [];
    if (v) { parts.push("pdk=" + v); }
    return href + (parts.length ? "?" + parts.join("&") : "") + hash;
  }

  function reflect() {                 // the address bar names the view (a copied link shows it)
    try {
      var url = withPdk(window.location.href, param());
      if (url !== window.location.href) { window.history.replaceState(window.history.state, "", url); }
    } catch (e) { /* file:// in some browsers: the view still changes */ }
  }

  // a link to another page of the site (an HTML <a> or an SVG <a>: the target is read as an attribute, since an SVG
  // <a>'s `target` property is an object)
  function isPage(a) {
    if (!a || !a.getAttribute || a.hasAttribute("download")) { return false; }
    var target = a.getAttribute("target");
    if (target && target !== "_self") { return false; }
    var href = a.getAttribute("href") || "";
    if (!href || href.charAt(0) === "#" || /^[a-z][a-z0-9+.-]*:/i.test(href)) { return false; }
    var path = href.split("#")[0].split("?")[0];
    return path === "" || /\.html$/.test(path) || /\/$/.test(path);
  }

  function carry(a) {                  // the link names the view the page shows
    if (!isPage(a)) { return; }
    var href = a.getAttribute("href"), to = withPdk(href, param());
    if (to !== href) { a.setAttribute("href", to); }
  }

  function carryAll() { Array.prototype.forEach.call(document.querySelectorAll("a[href]"), carry); }

  function selects() { return document.querySelectorAll("select[data-pdk-select]"); }

  function choose(v) {
    if (!known(v)) { return; }
    current = v;
    named = true;
    root.setAttribute("data-pdk", v);
    root.removeAttribute("data-pdk-moved");      // the reader chose: nothing to tell any more
    store(v);
    reflect();
    Array.prototype.forEach.call(selects(), function (s) { s.value = v; });
    carryAll();
  }

  function init() {
    reflect();
    Array.prototype.forEach.call(selects(), function (s) {
      s.value = current;
      var pick = s.closest("[data-pdk-pick]");
      if (pick) { pick.hidden = false; }
      s.addEventListener("change", function () { choose(s.value); });
    });
    carryAll();
    // a link drawn after this (a chart's dot, a redrawn explorer) is brought up to date before it is followed, opened
    // in a new tab (middle click: auxclick), copied (the context menu) or reached by the keyboard
    ["mousedown", "touchstart", "focusin", "click", "auxclick", "contextmenu"].forEach(function (type) {
      document.addEventListener(type, function (e) {
        carry(e.target && e.target.closest ? e.target.closest("a[href]") : null);
      }, { capture: true, passive: true });
    });
  }

  // a page the browser restores from its back-forward cache runs no script again: it takes up the latest choice here;
  // and the selectors show the view, whatever value a browser restored into them on Back
  window.addEventListener("pageshow", function (e) {
    var v = e && e.persisted ? stored() : null;
    if (v && v !== current) { choose(v); return; }
    Array.prototype.forEach.call(selects(), function (s) { s.value = current; });
  });

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
