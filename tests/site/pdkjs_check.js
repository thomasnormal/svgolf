// site/pdk.js's logic under a fake DOM (no browser, no libraries): the courses are sky130 and asap7pnr (ASAP7 placed and
// routed, 2026-11-12), and the old value asap7 is taken as asap7pnr with the notice mark; the URL's ?pdk= first, else the stored choice,
// else sky130 (Back and Forward: the stored choice first); storage that throws is tolerated; a choice is stored and
// put in the URL (?pdk=sky130 too once the reader has chosen); every link to the site's own pages carries it, an SVG
// <a> included, at load, on a choice and before a link is followed, opened in a new tab or copied.
//     node tests/site/pdkjs_check.js site/pdk.js        (test_pdk.PdkScriptTest runs it when node is installed)
const fs = require("fs");
const src = fs.readFileSync(process.argv[2], "utf8");
let fails = 0;
function ok(c, msg) { if (!c) { fails++; console.log("FAIL " + msg); } else { console.log("ok   " + msg); } }

// an <a>: `svg` gives it an SVG anchor's `target` property (an object, always truthy)
function anchor(href, { svg = false, attrs = {} } = {}) {
  const a = { attrs: Object.assign({ href }, attrs), target: svg ? { baseVal: "", animVal: "" } : (attrs.target || ""),
              hasAttribute(k) { return k in this.attrs; },
              getAttribute(k) { return k in this.attrs ? this.attrs[k] : null; },
              setAttribute(k, v) { this.attrs[k] = v; } };
  a.closest = () => a;
  return a;
}

function env({ url, stored, storageThrows = false, nav = "navigate", links = [] }) {
  const attrs = {}, listeners = {}, winListeners = {}, store = stored ? { "svgolf-pdk": stored } : {};
  const loc = new URL(url);
  const sel = { value: "sky130", listeners: {}, addEventListener(t, f) { this.listeners[t] = f; },
                closest() { return pick; } };
  const pick = { hidden: true };
  const window = {
    location: { get href() { return loc.href; }, get search() { return loc.search; } },
    localStorage: { getItem(k) { if (storageThrows) throw new Error("denied"); return k in store ? store[k] : null; },
                    setItem(k, v) { if (storageThrows) throw new Error("denied"); store[k] = v; } },
    history: { state: null, replaceState(s, t, u) { const n = new URL(u, loc.href); loc.href = n.href; } },
    performance: { getEntriesByType(t) { return t === "navigation" ? [{ type: nav }] : []; } },
    addEventListener(t, f) { winListeners[t] = f; },
  };
  const document = {
    readyState: "complete",
    documentElement: { setAttribute(k, v) { attrs[k] = v; }, getAttribute(k) { return attrs[k]; },
                       removeAttribute(k) { delete attrs[k]; } },
    querySelectorAll(q) {
      if (q.indexOf("data-pdk-select") >= 0) { return [sel]; }
      if (q === "a[href]") { return links; }
      return [];
    },
    addEventListener(t, f) { listeners[t] = f; },
  };
  new Function("window", "document", src)(window, document);
  return { attrs, store, loc, sel, pick, listeners, winListeners };
}

let e = env({ url: "http://x/tasks/add/index.html" });
ok(e.attrs["data-pdk"] === "sky130", "default sky130");
ok(e.loc.href === "http://x/tasks/add/index.html", "default: the URL stays clean");
ok(e.pick.hidden === false, "the selector is shown");
ok(!("svgolf-pdk" in e.store), "nothing is stored for a reader who never chose");

e = env({ url: "http://x/index.html?pdk=asap7pnr#tasks" });
ok(e.attrs["data-pdk"] === "asap7pnr", "?pdk=asap7pnr sets the view");
ok(e.store["svgolf-pdk"] === "asap7pnr", "a shared link's view is stored");
ok(e.sel.value === "asap7pnr", "the selector shows it");

e = env({ url: "http://x/index.html?pdk=ASAP7PNR" });
ok(e.attrs["data-pdk"] === "asap7pnr", "?pdk=ASAP7PNR (upper case) is the routed course");
ok(e.loc.href === "http://x/index.html?pdk=asap7pnr", "and the URL spells it as the site does: " + e.loc.href);

e = env({ url: "http://x/index.html", stored: "asap7pnr" });
ok(e.attrs["data-pdk"] === "asap7pnr", "the stored choice applies");
ok(e.loc.href === "http://x/index.html?pdk=asap7pnr", "and the URL names it: " + e.loc.href);

e = env({ url: "http://x/index.html?pdk=sky130", stored: "asap7pnr" });
ok(e.attrs["data-pdk"] === "sky130", "the URL wins over the stored choice");
ok(e.store["svgolf-pdk"] === "sky130", "and is stored");
ok(e.loc.href === "http://x/index.html?pdk=sky130", "a link that names sky130 keeps naming it: " + e.loc.href);

e = env({ url: "http://x/index.html", stored: "sky130" });
ok(e.attrs["data-pdk"] === "sky130", "a stored sky130");
ok(e.loc.href === "http://x/index.html?pdk=sky130",
   "the URL names it, so a copied link shows sky130 to a reader who chose ASAP7: " + e.loc.href);

e = env({ url: "http://x/index.html?pdk=asap7pnr", stored: "sky130", nav: "back_forward" });
ok(e.attrs["data-pdk"] === "sky130", "Back to a page whose URL says asap7pnr, after the reader chose sky130: sky130");
ok(e.store["svgolf-pdk"] === "sky130", "the reader's latest choice stays stored");
ok(e.loc.href === "http://x/index.html?pdk=sky130", "and the URL is brought up to date: " + e.loc.href);

e = env({ url: "http://x/index.html?pdk=asap7pnr", nav: "back_forward", storageThrows: true });
ok(e.attrs["data-pdk"] === "asap7pnr", "Back with storage refused: the URL is all there is");

for (const bad of ["constructor", "toString", "hasOwnProperty", "__proto__", "valueOf", "bogus"]) {
  e = env({ url: "http://x/a.html?x=1&pdk=" + bad });
  ok(e.attrs["data-pdk"] === "sky130", `?pdk=${bad} is no view: sky130`);
  ok(!("svgolf-pdk" in e.store), `?pdk=${bad} is not stored`);
  ok(e.sel.value === "sky130", `?pdk=${bad}: the selector shows sky130`);
  ok(e.loc.href === "http://x/a.html?x=1", `?pdk=${bad} is dropped from the URL: ` + e.loc.href);
}
e = env({ url: "http://x/a.html", stored: "constructor" });
ok(e.attrs["data-pdk"] === "sky130", "a stored value that is no view is ignored");

e = env({ url: "http://x/index.html", storageThrows: true });
ok(e.attrs["data-pdk"] === "sky130", "storage that throws: still works");
e.sel.value = "asap7pnr"; e.sel.listeners.change();
ok(e.attrs["data-pdk"] === "asap7pnr", "choosing ASAP7 switches the view without storage");
ok(e.loc.href === "http://x/index.html?pdk=asap7pnr", "and puts it in the URL");
e.sel.value = "sky130"; e.sel.listeners.change();
ok(e.loc.href === "http://x/index.html?pdk=sky130", "choosing sky130 after it names sky130 (a copied link keeps it)");

e = env({ url: "http://x/tasks/add/index.html?a=b#score" });
e.sel.value = "asap7pnr"; e.sel.listeners.change();
ok(e.store["svgolf-pdk"] === "asap7pnr", "choosing stores");
ok(e.loc.href === "http://x/tasks/add/index.html?a=b&pdk=asap7pnr#score", "other parameters and the fragment kept: " + e.loc.href);

// a link is brought up to date by the event `type` on it (capture listeners on the document)
function via(type, a) { e.listeners[type]({ target: a }); return a.attrs.href; }
function link(href, opts) { return via("click", anchor(href, opts)); }
ok(link("../mul/index.html") === "../mul/index.html?pdk=asap7pnr", "a page link carries the view");
ok(link("records/abc.html#dashboard") === "records/abc.html?pdk=asap7pnr#dashboard", "with its fragment");
ok(link("#score") === "#score", "an in-page link is left alone");
ok(link("https://example.org/") === "https://example.org/", "an external link is left alone");
ok(link("Spec.lean") === "Spec.lean", "a download is left alone");
ok(link("x.sv", { attrs: { download: "" } }) === "x.sv", "a download link is left alone");
ok(link("../mul/index.html", { attrs: { target: "_blank" } }) === "../mul/index.html",
   "a link to another window is left alone");
ok(link("records/d20b.html", { svg: true }) === "records/d20b.html?pdk=asap7pnr",
   "an SVG <a> (a chart's dot, its `target` an object) carries the view");
for (const type of ["mousedown", "touchstart", "focusin", "auxclick", "contextmenu"]) {
  ok(via(type, anchor("../mul/index.html", { svg: type === "contextmenu" })) === "../mul/index.html?pdk=asap7pnr",
     `${type} brings a link up to date (a middle click, a copied link, the keyboard)`);
}

const at = [anchor("../mul/index.html"), anchor("records/x.html", { svg: true }), anchor("#top"),
            anchor("https://example.org/"), anchor("../mul/index.html?pdk=asap7pnr")];
e = env({ url: "http://x/tasks/add/index.html?pdk=asap7pnr", links: at });
ok(at[0].attrs.href === "../mul/index.html?pdk=asap7pnr", "at load the page's own links carry the view");
ok(at[1].attrs.href === "records/x.html?pdk=asap7pnr", "an SVG <a> too");
ok(at[2].attrs.href === "#top" && at[3].attrs.href === "https://example.org/",
   "in-page and external links are not touched");
e.sel.value = "sky130"; e.sel.listeners.change();
ok(at[0].attrs.href === "../mul/index.html?pdk=sky130" && at[1].attrs.href === "records/x.html?pdk=sky130",
   "a choice rewrites them all");
ok(at[4].attrs.href === "../mul/index.html?pdk=sky130", "a carried parameter is replaced, not repeated");

const clean = [anchor("../mul/index.html?pdk=asap7pnr")];
e = env({ url: "http://x/tasks/add/index.html", links: clean });
ok(clean[0].attrs.href === "../mul/index.html", "a reader who never chose: a carried parameter is dropped");

// a page restored from the back-forward cache runs no script again: pageshow takes up the latest choice
e = env({ url: "http://x/index.html?pdk=asap7pnr", stored: "asap7pnr" });
e.store["svgolf-pdk"] = "sky130";                        // chosen on a later page
e.winListeners.pageshow({ persisted: true });
ok(e.attrs["data-pdk"] === "sky130", "restored from the back-forward cache: the latest choice applies");
ok(e.sel.value === "sky130", "and the selector shows it");
ok(e.loc.href === "http://x/index.html?pdk=sky130", "and the URL is brought up to date: " + e.loc.href);
e = env({ url: "http://x/index.html?pdk=asap7pnr" });
e.sel.value = "sky130";                                  // a value the browser restored into the selector on Back
e.winListeners.pageshow({ persisted: false });
ok(e.attrs["data-pdk"] === "asap7pnr", "an ordinary load's pageshow keeps the view");
ok(e.sel.value === "asap7pnr", "and sets the selector back to the view shown");

// the old value (2026-11-12: the cells-only ASAP7 view, replaced by the routed course): taken as asap7pnr, said so
e = env({ url: "http://x/tasks/add/index.html?pdk=asap7#score" });
ok(e.attrs["data-pdk"] === "asap7pnr", "an old ?pdk=asap7 link shows the routed course");
ok("data-pdk-moved" in e.attrs, "and marks the page, so that its notice says what changed");
ok(e.store["svgolf-pdk"] === "asap7pnr", "the course is stored under its new name");
ok(e.loc.href === "http://x/tasks/add/index.html?pdk=asap7pnr#score", "and the URL names it: " + e.loc.href);
ok(e.sel.value === "asap7pnr", "the selector shows it");
e = env({ url: "http://x/index.html?pdk=ASAP7" });
ok(e.attrs["data-pdk"] === "asap7pnr" && "data-pdk-moved" in e.attrs, "?pdk=ASAP7 (upper case) too");
e = env({ url: "http://x/index.html", stored: "asap7" });
ok(e.attrs["data-pdk"] === "asap7pnr", "an old stored choice shows the routed course");
ok("data-pdk-moved" in e.attrs, "and says so");
ok(e.store["svgolf-pdk"] === "asap7pnr", "it is stored under its new name, so the notice comes once");
ok(e.loc.href === "http://x/index.html?pdk=asap7pnr", "and the URL names it: " + e.loc.href);
e = env({ url: "http://x/index.html?pdk=sky130", stored: "asap7" });
ok(e.attrs["data-pdk"] === "sky130" && !("data-pdk-moved" in e.attrs), "a link to sky130 wins, and nothing is said");
e = env({ url: "http://x/index.html?pdk=asap7" });
e.sel.value = "sky130"; e.sel.listeners.change();
ok(e.attrs["data-pdk"] === "sky130" && !("data-pdk-moved" in e.attrs), "a choice removes the notice mark");
e = env({ url: "http://x/index.html" });
ok(!("data-pdk-moved" in e.attrs), "a reader who never chose: no notice");
e = env({ url: "http://x/index.html?pdk=asap7pnr" });
ok(!("data-pdk-moved" in e.attrs), "a link that names the routed course: no notice");
const old = [anchor("../mul/index.html?pdk=asap7")];
e = env({ url: "http://x/tasks/add/index.html?pdk=asap7", links: old });
ok(old[0].attrs.href === "../mul/index.html?pdk=asap7pnr", "a page link that carried the old value carries the new one");

console.log(fails ? `${fails} FAILED` : "all ok");
process.exit(fails ? 1 : 0);
