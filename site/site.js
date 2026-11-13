// svGolf site: the one shared script. Every page reads without it; it adds a copy button to each
// code block (page.py's code_block and the Markdown renderer emit `pre.code`) and turns a task
// page's property panel and a detail page's netlist card into tabs (with the links into their panes: a
// second click on a link whose fragment the URL already names still shows its pane). No libraries, nothing
// fetched.
(function () {
  "use strict";

  function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) {
      return navigator.clipboard.writeText(text);
    }
    return new Promise(function (resolve, reject) {     // file:// and plain http: a hidden textarea
      var ta = document.createElement("textarea");
      ta.value = text;
      ta.setAttribute("readonly", "");
      ta.style.position = "fixed";
      ta.style.opacity = "0";
      document.body.appendChild(ta);
      ta.select();
      try {
        document.execCommand("copy") ? resolve() : reject(new Error("copy refused"));
      } catch (e) {
        reject(e);
      } finally {
        document.body.removeChild(ta);
      }
    });
  }

  function addCopy(pre) {
    var box = pre.parentElement;
    if (!box || !box.classList.contains("codebox")) {
      box = document.createElement("div");
      box.className = "codebox";
      pre.parentNode.insertBefore(box, pre);
      box.appendChild(pre);
    }
    var btn = document.createElement("button");
    btn.type = "button";
    btn.className = "copy";
    btn.textContent = "Copy";
    btn.setAttribute("aria-label", "Copy the code to the clipboard");
    btn.addEventListener("click", function () {
      var code = pre.querySelector("code") || pre;
      copyText(code.textContent).then(function () {
        btn.textContent = "Copied";
        btn.classList.add("done");
        setTimeout(function () { btn.textContent = "Copy"; btn.classList.remove("done"); }, 1600);
      }, function () {
        btn.textContent = "Select and copy";
      });
    });
    var actions = box.querySelector(":scope > .codebox-head .codebox-actions");
    if (actions) {
      actions.appendChild(btn);
    } else {
      box.appendChild(btn);
    }
  }

  // The property panel (page.py's props_panel): its tab links become tabs. Without this script the
  // links jump to panes that stand one under the other. A link or a URL fragment that names a pane, or
  // something inside one (a card: #prop-COMPUTES_SUM, #def-SvGolf.HoldAll; a group: #reject-at-proof), shows
  // that pane and opens the card.
  function initTabs(panel) {
    var tabs = Array.prototype.slice.call(panel.querySelectorAll(     // the panel's tabs, or a card's (page.py's
      ":scope > .props-head > .props-tabs > a[href^='#'], " +         // tabs: a detail page's netlist)
      ":scope > .tabs-nav > a[href^='#']"));
    var panes = tabs.map(function (tab) { return document.getElementById(tab.getAttribute("href").slice(1)); });
    if (tabs.length < 2 || panes.some(function (p) { return !p; })) {
      return null;
    }
    panel.classList.add("js-tabs");
    var list = tabs[0].parentNode;
    list.setAttribute("role", "tablist");
    // a tab its course hides (the routed course's Layout on sky130: style.css hides `.pdk-asap7pnr`) is never the one
    // shown; when the reader changes the course (pdk.js sets <html data-pdk>), a pane that left is replaced by the first
    function shown(k) {
      return window.getComputedStyle(tabs[k]).display !== "none";
    }
    function usable(k) {
      if (k >= 0 && shown(k)) { return k; }
      for (var j = 0; j < tabs.length; j++) { if (shown(j)) { return j; } }
      return 0;
    }

    tabs.forEach(function (tab, k) {
      tab.setAttribute("role", "tab");
      tab.id = tab.id || panes[k].id + "-tab";
      tab.setAttribute("aria-controls", panes[k].id);
      panes[k].setAttribute("role", "tabpanel");
      panes[k].setAttribute("aria-labelledby", tab.id);
    });

    // a pane scrolled to (by a link, the URL's fragment or the browser's own scroll to it) leaves the tabs above
    // it in view: its scroll margin is the height of the panel's head
    function margin(k) {
      var gap = panes[k].getBoundingClientRect().top - panel.getBoundingClientRect().top;
      panes[k].style.scrollMarginTop = Math.max(0, Math.round(gap)) + "px";
    }

    var current = 0;
    function select(k, focus) {
      k = usable(k);
      current = k;
      tabs.forEach(function (tab, j) {
        tab.setAttribute("aria-selected", j === k ? "true" : "false");
        tab.tabIndex = j === k ? 0 : -1;
        panes[j].hidden = j !== k;
      });
      margin(k);
      if (focus) {
        tabs[k].focus();
      }
    }

    function choose(k, focus) {          // a reader's choice of tab: the URL names the pane shown, for a reload
      select(k, focus);
      if (window.history && history.replaceState) {
        history.replaceState(history.state, "", "#" + panes[current].id);
      }
    }

    tabs.forEach(function (tab, k) {
      tab.addEventListener("click", function (e) {
        e.preventDefault();
        choose(k, false);
      });
      tab.addEventListener("keydown", function (e) {
        var to = { ArrowRight: k + 1, ArrowLeft: k - 1, Home: 0, End: tabs.length - 1 }[e.key];
        if (to === undefined) {
          return;
        }
        e.preventDefault();
        var step = to < k || e.key === "End" ? -1 : 1, n = (to + tabs.length) % tabs.length;
        for (var i = 0; i < tabs.length && !shown(n); i++) { n = (n + step + tabs.length) % tabs.length; }
        choose(n, true);
      });
    });
    select(0, false);
    if (window.MutationObserver) {
      new MutationObserver(function () {
        if (!shown(current)) { select(0, false); }
      }).observe(document.documentElement, { attributes: true, attributeFilter: ["data-pdk"] });
    }

    // show the pane holding `el` and scroll to it (its card is open already: bring); false when `el` is in no
    // pane of this panel. The browser cannot scroll to a hidden pane, so this does; a pane its course hides is not
    // shown (the first tab is) and nothing is scrolled to.
    return function reveal(el) {
      var k = panes.findIndex(function (p) { return p === el || p.contains(el); });
      if (k < 0) {
        return false;
      }
      select(k, false);
      if (current === k) { el.scrollIntoView(); }
      return true;
    };
  }

  function fragment(hash) {
    try {
      return decodeURIComponent(hash.slice(1));
    } catch (e) {
      return hash.slice(1);
    }
  }

  // the element a fragment names: show it if a tab hides it, open the disclosures around it; true when this
  // script scrolled to it (a pane's content), false when the browser's own scroll is to follow
  function bring(id, reveals) {
    var el = id && document.getElementById(id);
    if (!el) {
      return false;
    }
    for (var d = el.closest("details"); d; d = d.parentElement && d.parentElement.closest("details")) {
      d.open = true;                     // "The proof in detail", a property's card, ...
    }
    return reveals.some(function (r) { return r(el); });
  }

  function init() {
    Array.prototype.forEach.call(document.querySelectorAll("pre.code"), addCopy);
    var reveals = Array.prototype.map.call(document.querySelectorAll(".props[data-tabs], .tabs[data-tabs]"), initTabs)
      .filter(Boolean);
    window.addEventListener("hashchange", function () { bring(fragment(location.hash), reveals); });
    // a link to this page's own fragment: the browser does nothing when the URL already names it (a second
    // click on "what does not count" after a tab was chosen), and does not scroll to a hidden pane
    document.addEventListener("click", function (e) {
      if (e.defaultPrevented || e.button !== 0 || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey) {
        return;
      }
      var a = e.target.closest && e.target.closest("a[href^='#']");
      if (!a || a.getAttribute("href").length < 2) {
        return;
      }
      var hash = a.getAttribute("href");
      if (bring(fragment(hash), reveals)) {
        e.preventDefault();
        if (location.hash !== hash && window.history && history.pushState) {
          history.pushState(null, "", hash);
        }
      }
    });
    bring(fragment(location.hash), reveals);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
