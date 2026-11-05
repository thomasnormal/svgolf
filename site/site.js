// svGolf site: the one shared script. Every page reads without it; it adds a copy button to each
// code block (page.py's code_block and the Markdown renderer emit `pre.code`) and turns a task
// page's property panel into tabs. No libraries, nothing fetched.
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
  // links jump to panes that stand one under the other. A URL fragment that names something inside
  // a pane (a card: #prop-COMPUTES_SUM, #def-SvGolf.HoldAll) shows that pane and opens the card.
  function initTabs(panel) {
    var tabs = Array.prototype.slice.call(panel.querySelectorAll(".props-tabs > a[href^='#']"));
    var panes = tabs.map(function (tab) { return document.getElementById(tab.getAttribute("href").slice(1)); });
    if (tabs.length < 2 || panes.some(function (p) { return !p; })) {
      return null;
    }
    panel.classList.add("js-tabs");
    var list = panel.querySelector(".props-tabs");
    list.setAttribute("role", "tablist");
    tabs.forEach(function (tab, k) {
      tab.setAttribute("role", "tab");
      tab.id = tab.id || panes[k].id + "-tab";
      tab.setAttribute("aria-controls", panes[k].id);
      panes[k].setAttribute("role", "tabpanel");
      panes[k].setAttribute("aria-labelledby", tab.id);
    });

    function select(k, focus) {
      tabs.forEach(function (tab, j) {
        tab.setAttribute("aria-selected", j === k ? "true" : "false");
        tab.tabIndex = j === k ? 0 : -1;
        panes[j].hidden = j !== k;
      });
      if (focus) {
        tabs[k].focus();
      }
    }

    tabs.forEach(function (tab, k) {
      tab.addEventListener("click", function (e) {
        e.preventDefault();
        select(k, false);
      });
      tab.addEventListener("keydown", function (e) {
        var to = { ArrowRight: k + 1, ArrowLeft: k - 1, Home: 0, End: tabs.length - 1 }[e.key];
        if (to === undefined) {
          return;
        }
        e.preventDefault();
        select((to + tabs.length) % tabs.length, true);
      });
    });
    select(0, false);

    return function reveal(id) {             // show the pane holding #id and open its card
      var el = id && document.getElementById(id);
      if (!el || !panel.contains(el)) {
        return;
      }
      var k = panes.findIndex(function (p) { return p === el || p.contains(el); });
      if (k >= 0) {
        select(k, false);
      }
      var card = el.closest("details");
      if (card) {
        card.open = true;
      }
      if (el !== panes[k]) {
        el.scrollIntoView();
      }
    };
  }

  function fragment() {
    try {
      return decodeURIComponent(location.hash.slice(1));
    } catch (e) {
      return location.hash.slice(1);
    }
  }

  function init() {
    Array.prototype.forEach.call(document.querySelectorAll("pre.code"), addCopy);
    var reveals = Array.prototype.map.call(document.querySelectorAll(".props[data-tabs]"), initTabs)
      .filter(Boolean);
    if (reveals.length) {
      var show = function () { reveals.forEach(function (r) { r(fragment()); }); };
      window.addEventListener("hashchange", show);
      show();
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
