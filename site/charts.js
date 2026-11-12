// svGolf site: the charts of a task page. The page reads without this script: the server draws the
// score chart (on a linear and on a log axis) and the explorer's first pair of metrics as SVG
// (svgplot.py), with the same numbers in tables under them. This script only adds:
//   * the linear/log switch of the score chart (it shows one of the two drawings);
//   * tooltips for the marks of every chart and the score chart's baseline levels (from each
//     one's data-tip; designs drawn at one point share one tooltip that names them all);
//   * the explorer: the point selector (the scored point's ranked numbers, or another point's
//     measured ones: score/measured/<task>.json), two axis menus and their log switches, and a redraw
//     of the scatter from the page's data (the inert JSON in #task-data; the ASAP7 view's explorer, a
//     second copy on the page, from #task-data-asap7: site/build.py `dual`), with the Pareto front of
//     the proved designs for the chosen pair. The drawing mirrors svgplot.scatter_chart: same frame,
//     scales, ticks, marks and CSS classes.
//   * the scaling view: a metric menu, the "÷ par" and log switches, and a redraw of the lines
//     (svgplot.line_chart's frame, scales, marks, margin names and classes).
//   * a detail page (a record's, a reference's): the area-time plot's "fit to cluster" / "all designs"
//     switch (it shows one of the server's two drawings) and the schematic's zoom buttons (they scale
//     the inline SVG inside its scroll box about the view's centre), critical-path switch, cell finder
//     and the critical-path links into the drawing (the drawing sits in the netlist card's Schematic tab:
//     a link from the Critical path tab opens it first; site.js makes the tabs).
// No libraries, nothing fetched.
(function () {
  "use strict";

  // svgplot.SCATTER_FRAME and SCATTER_COMPACT (a box narrower than COMPACT_BELOW px gets the latter)
  var FRAMES = {
    wide: { w: 960, h: 430, left: 82, right: 24, top: 18, bottom: 56, ticks: 6 },
    compact: { w: 420, h: 400, left: 60, right: 16, top: 32, bottom: 52, ticks: 4 }
  };
  var COMPACT_BELOW = 720;              // style.css switches the server's drawings at 52rem
  var INTEGER = { depth: 1, cycles: 1, ffs: 1, gates: 1, proof_lines: 1 };
  var KIND_ORDER = { baseline: 0, reference: 1, record: 2 };
  var KIND_TEXT = { record: "submission", reference: "proved reference", baseline: "baseline, not proved" };
  var MEASURED = "measured, not ranked";
  // svgplot.LINES_FRAME and LINES_COMPACT (the scaling view)
  var LINE_FRAMES = {
    wide: { w: 960, h: 430, left: 82, right: 196, top: 18, bottom: 56, ticks: 6, gap: 15, chars: 26, charW: 6.6 },
    compact: { w: 420, h: 400, left: 60, right: 116, top: 32, bottom: 52, ticks: 4, gap: 16, chars: 13, charW: 9.0 }
  };

  function esc(s) {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }

  function f1(v) {                      // a coordinate, rounded to 0.1 (as svgplot._f)
    var s = (Math.round(v * 10) / 10).toFixed(1);
    return s === "-0.0" ? "0.0" : s;
  }

  function group(intText) {             // thin-space thousands groups (as the server prints them)
    return intText.replace(/\B(?=(\d{3})+(?!\d))/g, " ");
  }

  function sig(v, n) {                  // n significant digits, trailing zeros dropped (Python's %g)
    return String(Number(v.toPrecision(n)));
  }

  function num(v) {                     // a tick label (svgplot.tick: num's form, as many digits as make it exact)
    var a = Math.abs(v), scale = a >= 1e6 ? 1e6 : a >= 1e4 ? 1e3 : 1, unit = a >= 1e6 ? "M" : a >= 1e4 ? "k" : "";
    for (var d = unit ? 3 : 4; d < 10; d++) {
      var s = sig(v / scale, d);
      if (Math.abs(Number(s) * scale - v) <= 1e-9 * Math.max(1, a)) { return s + unit; }
    }
    return sig(v / scale, 10) + unit;
  }

  function tickRows(xs, labels, charW) {   // svgplot.tick_rows: a label overlapping the one before drops a row
    var rows = [], ends = [-Infinity, -Infinity], gap = 6;
    xs.forEach(function (x, k) {
      var half = labels[k].length * charW / 2;
      var row = x - half >= ends[0] + gap ? 0 : (x - half >= ends[1] + gap ? 1 : 0);
      rows.push(row);
      ends[row] = x + half;
    });
    return rows;
  }

  function fmtMetric(m, v) {            // a metric's value as text (metrics.Metric.fmt)
    if (v === undefined || v === null) { return "–"; }
    if (m.key === "adp") {
      if (v >= 10000) { return group(String(Math.round(v))); }
      if (v >= 1000) { return String(Math.round(v)); }
      return v >= 1 ? sig(v, 4) : sig(v, 3);
    }
    var s = m.digits ? v.toFixed(m.digits) : String(Math.round(v));
    if (Math.abs(v) >= 10000) {
      var parts = s.split(".");
      s = group(parts[0]) + (parts.length > 1 ? "." + parts[1] : "");
    }
    return s;
  }

  var Y_BETTER = " · lower is better";   // svgplot.Y_BETTER: every plotted number is minimized
  function axisLabel(m) { return m.unit ? m.label + " (" + m.unit + ")" : m.label; }

  function gnum(v) { return String(Number(v.toPrecision(6))); }    // Python's :g for a radius

  // -- scales (svgplot.Scale) -----------------------------------------------------------------

  function niceStep(span, target) {
    var raw = span / Math.max(1, target);
    var mag = raw > 0 ? Math.pow(10, Math.floor(Math.log10(raw))) : 1;
    var ms = [1, 2, 2.5, 5, 10];
    for (var i = 0; i < ms.length; i++) { if (raw <= ms[i] * mag) { return ms[i] * mag; } }
    return 10 * mag;
  }

  function Scale(lo, hi, px0, px1, opt) {
    opt = opt || {};
    if (lo > hi) { var t = lo; lo = hi; hi = t; }
    this.log = opt.log === undefined ? (lo > 0 && hi / lo > 10) : (opt.log && lo > 0);
    this.integer = !!opt.integer;
    var nonneg = lo >= 0;
    if (this.log) {
      if (hi / lo > 1.5) { lo = lo / 1.25; hi = hi * 1.25; } else { lo = lo / 1.12; hi = hi * 1.12; }
    } else if (hi === lo) {
      var pad = this.integer ? 1 : (Math.abs(lo) * 0.1 || 1);
      lo -= pad; hi += pad;
    } else {
      var p = (hi - lo) * 0.08;
      lo -= p; hi += p;
    }
    if (this.integer && !this.log) { lo = Math.floor(lo); hi = Math.ceil(hi); }
    if (nonneg && !this.log) { lo = Math.max(0, lo); }
    this.lo = lo; this.hi = hi; this.px0 = px0; this.px1 = px1;
  }

  Scale.prototype.map = function (v) {
    var a, b;
    if (this.log) { a = Math.log10(this.lo); b = Math.log10(this.hi); v = Math.log10(v); } else { a = this.lo; b = this.hi; }
    return this.px0 + (v - a) / (b - a) * (this.px1 - this.px0);
  };

  Scale.prototype.ticks = function (target) {
    var out, v;
    if (this.log) {
      var e0 = Math.floor(Math.log10(this.lo)), e1 = Math.ceil(Math.log10(this.hi));
      var sets = [[1], [1, 2, 5], [1, 2, 3, 4, 5, 6, 7, 8, 9]];
      for (var s = 0; s < sets.length; s++) {
        out = [];
        for (var e = e0; e <= e1; e++) {
          for (var k = 0; k < sets[s].length; k++) {
            v = sets[s][k] * Math.pow(10, e);
            if (this.lo <= v && v <= this.hi) { out.push(v); }
          }
        }
        if (out.length >= 3) {          // thinned to about target + 2 (svgplot.Scale.ticks)
          var every = Math.max(1, Math.ceil(out.length / Math.max(4, (target || 6) + 2)));
          return out.filter(function (_, i) { return i % every === 0; });
        }
      }
    }
    var step = niceStep(this.hi - this.lo, target || 6);
    if (this.integer) { step = Math.max(1, Math.round(step)); }
    out = [];
    for (v = Math.ceil(this.lo / step) * step; v <= this.hi + 1e-9; v += step) {
      if (!this.log || v > 0) { out.push(Math.round(v * 1e6) / 1e6); }
    }
    return out;
  };

  // -- drawing (svgplot.scatter_chart) --------------------------------------------------------

  function marker(kind, x, y, banned, r) {   // svgplot.marker (r: the base radius, 5 by default)
    var X = f1(x), Y = f1(y);
    r = r || 5;
    if (kind === "record") { return '<circle class="m-record" cx="' + X + '" cy="' + Y + '" r="' + gnum(r * 1.3) + '"/>'; }
    if (kind === "reference") {
      return '<circle class="m-reference-ring" cx="' + X + '" cy="' + Y + '" r="' + gnum(r * 1.5) + '"/>' +
             '<circle class="m-reference" cx="' + X + '" cy="' + Y + '" r="' + gnum(r * 0.7) + '"/>';
    }
    var c = '<circle class="m-baseline" cx="' + X + '" cy="' + Y + '" r="' + gnum(r) + '"/>';
    if (banned) {
      c += '<path class="m-banned" d="M' + f1(x - 6) + " " + f1(y - 6) + "L" + f1(x + 6) + " " + f1(y + 6) +
           "M" + f1(x - 6) + " " + f1(y + 6) + "L" + f1(x + 6) + " " + f1(y - 6) + '"/>';
    }
    return c;
  }

  function stepPoints(front) {          // the staircase through a minimization front, by x
    var pts = front.slice().sort(function (a, b) { return a[0] - b[0] || a[1] - b[1]; })
      .filter(function (p, k, all) { return !k || p[0] !== all[k - 1][0] || p[1] !== all[k - 1][1]; });  // as a set
    var out = [];
    pts.forEach(function (p, k) {
      if (k) { out.push([p[0], pts[k - 1][1]]); }
      out.push(p);
    });
    return out;
  }

  function paretoIds(points) {          // proved points no other proved point beats on both axes
    var proved = points.filter(function (p) { return p.kind !== "baseline"; });
    var on = {};
    proved.forEach(function (p) {
      var beaten = proved.some(function (q) {
        return q.x <= p.x && q.y <= p.y && (q.x < p.x || q.y < p.y);
      });
      if (!beaten) { on[p.id] = true; }
    });
    return on;
  }

  function kindText(d) {
    return KIND_TEXT[d.kind] + (d.par ? " · par" : "") + (d.banned ? " · banned operator" : "") +
           (d.measured ? " · " + MEASURED : "");
  }

  function sharedTips(pts, on) {        // designs at one (x, y) share one tooltip (svgplot.shared_tips)
    var groups = {};
    pts.forEach(function (p) { (groups[p.x + "," + p.y] = groups[p.x + "," + p.y] || []).push(p); });
    Object.keys(groups).forEach(function (k) {
      var g = groups[k];
      if (g.length < 2) { return; }
      g = g.slice().sort(function (a, b) {
        return (!!on[b.id] - !!on[a.id]) || (KIND_ORDER[b.kind] - KIND_ORDER[a.kind]) ||
               (a.id < b.id ? -1 : a.id > b.id ? 1 : 0);
      });
      var tip = [g.length + " designs at this point"].concat(g.map(function (q) { return q.brief; }), g[0].axisTip);
      g.forEach(function (q) { q.tip = tip; });
    });
  }

  function tipLines(d, ms) {
    var out = [d.name, kindText(d) + (d.date ? " · " + d.date.slice(0, 10) : "")];
    ms.forEach(function (m) {
      if (m && d.m[m.key] !== undefined) {
        out.push(m.label + ": " + fmtMetric(m, d.m[m.key]) + (m.unit ? " " + m.unit : ""));
      }
    });
    return out;
  }

  // view: {task, metrics, designs, where}: `where` (a measured point's name) goes into the title
  function drawScatter(data, xk, yk, xlog, ylog, compact) {
    var F = compact ? FRAMES.compact : FRAMES.wide, W = F.w, H = F.h;
    var byKey = {};
    data.metrics.forEach(function (m) { byKey[m.key] = m; });
    var mx = byKey[xk], my = byKey[yk];
    var pts = data.designs.filter(function (d) {
      return d.m[xk] !== undefined && d.m[yk] !== undefined;
    }).map(function (d) {
      return { id: d.id, kind: d.kind, banned: d.banned, href: d.href, x: d.m[xk], y: d.m[yk], name: d.name,
               tip: tipLines(d, [byKey.adp, mx, my]), brief: d.name + " · " + kindText(d),
               axisTip: tipLines(d, [mx, my]).slice(2) };
    });
    if (!pts.length) { return { svg: "", n: 0 }; }
    var left = F.left, right = W - F.right, top = F.top, bottom = H - F.bottom;
    var xv = pts.map(function (p) { return p.x; }), yv = pts.map(function (p) { return p.y; });
    var xs = new Scale(Math.min.apply(null, xv), Math.max.apply(null, xv), left, right, { log: xlog, integer: !!INTEGER[xk] });
    var ys = new Scale(Math.min.apply(null, yv), Math.max.apply(null, yv), bottom, top, { log: ylog, integer: !!INTEGER[yk] });
    var xt = axisLabel(mx) + (xs.log ? ", log scale" : ""), yt = axisLabel(my) + (ys.log ? ", log scale" : "") + Y_BETTER;
    var title = data.task + (data.where ? " at " + data.where + " (" + MEASURED + ")" : "") + ": " +
                my.label.toLowerCase() + " against " + mx.label.toLowerCase();
    var s = ['<svg class="chart' + (compact ? " compact" : "") + '" viewBox="0 0 ' + W + " " + H + '" role="img" aria-label="' + esc(title) +
             '" xmlns="http://www.w3.org/2000/svg"><title>' + esc(title) + "</title><desc>" + esc(pts.length +
             (pts.length === 1 ? " design by " : " designs by ") + axisLabel(mx) + " (x) and " + axisLabel(my) +
             " (y); lower is better on both.") +
             '</desc><g class="axes">'];
    ys.ticks(F.ticks).forEach(function (v) {
      var y = ys.map(v);
      s.push('<line class="grid" x1="' + f1(left) + '" x2="' + f1(right) + '" y1="' + f1(y) + '" y2="' + f1(y) + '"/>' +
             '<text class="tick" x="' + f1(left - 8) + '" y="' + f1(y + 4) + '" text-anchor="end">' + esc(num(v)) + "</text>");
    });
    xs.ticks(F.ticks).forEach(function (v) {
      var x = xs.map(v);
      s.push('<line class="grid" x1="' + f1(x) + '" x2="' + f1(x) + '" y1="' + f1(top) + '" y2="' + f1(bottom) + '"/>' +
             '<text class="tick" x="' + f1(x) + '" y="' + f1(bottom + 18) + '" text-anchor="middle">' + esc(num(v)) + "</text>");
    });
    s.push('<line class="axis" x1="' + f1(left) + '" x2="' + f1(right) + '" y1="' + f1(bottom) + '" y2="' + f1(bottom) + '"/>' +
           '<line class="axis" x1="' + f1(left) + '" x2="' + f1(left) + '" y1="' + f1(top) + '" y2="' + f1(bottom) + '"/>' +
           '<text class="axis-title" x="' + f1((left + right) / 2) + '" y="' + f1(H - 8) + '" text-anchor="middle">' + esc(xt) + "</text>" +
           (compact ? '<text class="axis-title" x="4.0" y="' + f1(top - 12) + '" text-anchor="start">' :
            '<text class="axis-title" transform="translate(14 ' + f1((top + bottom) / 2) + ') rotate(-90)" text-anchor="middle">') +
           esc(yt) + "</text></g>");
    var on = paretoIds(pts);
    sharedTips(pts, on);
    var front = pts.filter(function (p) { return on[p.id]; }).map(function (p) { return [p.x, p.y]; });
    if (front.length) {
      var stair = stepPoints(front);
      var coords = f1(xs.map(stair[0][0])) + "," + f1(top) + " " +
                   stair.map(function (p) { return f1(xs.map(p[0])) + "," + f1(ys.map(p[1])); }).join(" ") +
                   " " + f1(right) + "," + f1(ys.map(stair[stair.length - 1][1]));
      s.push('<polyline class="frontier" points="' + coords + '"><title>the Pareto front of the proved designs</title></polyline>');
    }
    pts.sort(function (a, b) {
      return (!!on[a.id] - !!on[b.id]) || (KIND_ORDER[a.kind] - KIND_ORDER[b.kind]) || (a.y - b.y) || (a.x - b.x) ||
             (a.id < b.id ? -1 : a.id > b.id ? 1 : 0);
    });
    pts.forEach(function (p) {
      var x = xs.map(p.x), y = ys.map(p.y);
      var g = '<g class="mark ' + (on[p.id] ? "on-front" : "off-front") + '" data-kind="' + esc(p.kind) +
              '" data-id="' + esc(p.id) + '" data-tip="' + esc(p.tip.join("\n")) + '">' +
              '<circle class="hit" cx="' + f1(x) + '" cy="' + f1(y) + '" r="12"/>' + marker(p.kind, x, y, p.banned) + "</g>";
      s.push(p.href ? '<a href="' + esc(p.href) + '" aria-label="' + esc(p.name) + '">' + g + "</a>" : g);
    });
    s.push("</svg>");
    return { svg: s.join(""), n: pts.length, xlog: xs.log, ylog: ys.log };
  }

  // -- tooltips -------------------------------------------------------------------------------

  function tipFor(box) {
    var tip = box.querySelector(":scope > .chart-tip");
    if (!tip) {
      tip = document.createElement("div");
      tip.className = "chart-tip";
      tip.setAttribute("role", "status");
      tip.hidden = true;
      box.appendChild(tip);
    }
    return tip;
  }

  function showTip(box, mark, clientX) {
    var lines = (mark.getAttribute("data-tip") || "").split("\n");
    var tip = tipFor(box);
    tip.textContent = "";
    lines.forEach(function (ln, i) {
      var el = document.createElement(i === 0 ? "strong" : "span");
      el.textContent = ln;
      tip.appendChild(el);
    });
    tip.hidden = false;
    var dot = mark.querySelector(".hit") || mark;
    var r = dot.getBoundingClientRect(), b = box.getBoundingClientRect();
    // a level runs across the chart: its tip goes where the pointer is on it
    var cx = mark.classList.contains("level-mark") && clientX !== undefined ? clientX : r.left + r.width / 2;
    var x = cx - b.left + box.scrollLeft, y = r.top - b.top + box.scrollTop;
    var w = tip.offsetWidth, maxX = box.scrollWidth - w - 4;
    tip.style.left = Math.max(4, Math.min(maxX, x - w / 2)) + "px";
    var above = y - tip.offsetHeight - 2;
    tip.style.top = (above >= 0 ? above : y + r.height + 2) + "px";
  }

  function wireTips(box) {
    function hide() { var t = box.querySelector(":scope > .chart-tip"); if (t) { t.hidden = true; } }
    // a mark, a baseline's level and a baseline's label in the margin each carry a data-tip
    function tipped(el) { return el && el.closest ? el.closest("svg [data-tip]") : null; }
    box.addEventListener("pointerover", function (e) {
      var mark = tipped(e.target);
      if (mark) { showTip(box, mark, e.clientX); }
    });
    box.addEventListener("pointerleave", hide);
    box.addEventListener("pointerout", function (e) {
      var from = tipped(e.target);
      if (from && tipped(e.relatedTarget) !== from) { hide(); }
    });
    box.addEventListener("focusin", function (e) {
      var mark = e.target.querySelector ? e.target.querySelector(".mark[data-tip]") : null;
      if (mark) { showTip(box, mark); }
    });
    box.addEventListener("focusout", hide);
  }

  function dropTitles(box) {            // the script's tooltip replaces the browser's (no double tips)
    Array.prototype.forEach.call(box.querySelectorAll("[data-tip] > title"), function (t) { t.remove(); });
  }

  // -- the score chart's switch ---------------------------------------------------------------

  function wireScale(toggle) {         // the card holds the chart once per library view (site/build.py `dual`)
    var card = toggle.closest("section") || document;
    var boxes = card.querySelectorAll("[data-score-chart]");
    if (!boxes.length) { return; }
    toggle.hidden = false;
    var buttons = toggle.querySelectorAll("button");
    Array.prototype.forEach.call(buttons, function (btn, i) {
      btn.addEventListener("click", function () {
        Array.prototype.forEach.call(buttons, function (b, j) { b.setAttribute("aria-pressed", i === j ? "true" : "false"); });
        Array.prototype.forEach.call(boxes, function (box) {
          Array.prototype.forEach.call(box.querySelectorAll("[data-scale]"), function (v) {
            v.hidden = v.getAttribute("data-scale") !== (i === 0 ? "linear" : "log");
          });
          var t = box.querySelector(":scope > .chart-tip");
          if (t) { t.hidden = true; }
        });
      });
    });
  }

  // -- a detail page: the area-time plot's view switch, the schematic's zoom ------------------

  function wireViewToggle(toggle) {      // "Fit to cluster" / "All designs": shows one of the server's drawings
    var slot = toggle.closest("[data-hook]") || document;
    var box = slot.querySelector("[data-area-time]");
    if (!box) { return; }
    toggle.hidden = false;
    var buttons = toggle.querySelectorAll("button");
    Array.prototype.forEach.call(buttons, function (btn, i) {
      btn.addEventListener("click", function () {
        Array.prototype.forEach.call(buttons, function (b, j) { b.setAttribute("aria-pressed", i === j ? "true" : "false"); });
        Array.prototype.forEach.call(box.querySelectorAll("[data-view]"), function (v) {
          v.hidden = v.getAttribute("data-view") !== (i === 0 ? "fit" : "all");
        });
        var t = box.querySelector(":scope > .chart-tip");
        if (t) { t.hidden = true; }
      });
    });
  }

  // The drawing in a scroll box (without the script: shrunk to the box's width, and each cell a link target). The
  // script adds zoom about the view's centre (the critical path keeps its width when the drawing is shown smaller
  // than its size), a cell finder (instance or cell type; Enter steps through the hits), and the critical-path links
  // (`a.sch-link`, to `#sch-<instance>`), which scroll the cell to the middle of the view and mark it. The drawing
  // is in a tab (page.py's tabs): it is fitted the first time it is shown, and a link from another tab opens its
  // tab first (by clicking the tab, so site.js keeps the tabs' state).
  function wireSchematic(box) {
    var svg = box.querySelector("svg.sch");
    var tools = box.parentNode.querySelector("[data-schematic-tools]");
    if (!svg || !tools) { return; }
    var w0 = parseFloat(svg.getAttribute("width")), h0 = parseFloat(svg.getAttribute("height"));
    if (!(w0 > 0 && h0 > 0)) { return; }
    var zoom = 1;
    box.classList.add("zoomable");
    function origin() {                  // where the drawing's (0, 0) is in the box's scrolled content
      var b = box.getBoundingClientRect(), s = svg.getBoundingClientRect();
      return { x: s.left - b.left - box.clientLeft + box.scrollLeft, y: s.top - b.top - box.clientTop + box.scrollTop };
    }
    function set(z) {                    // the point of the drawing at the view's centre stays there
      var o = origin(), vx = box.clientWidth / 2, vy = box.clientHeight / 2;
      var px = (box.scrollLeft + vx - o.x) / zoom, py = (box.scrollTop + vy - o.y) / zoom;
      zoom = Math.max(0.05, Math.min(8, z));
      svg.setAttribute("width", String(Math.round(w0 * zoom)));
      svg.setAttribute("height", String(Math.round(h0 * zoom)));
      box.classList.toggle("zoomed-out", zoom < 0.75);
      o = origin();
      box.scrollLeft = o.x + px * zoom - vx;
      box.scrollTop = o.y + py * zoom - vy;
    }
    function fit() {
      set(Math.min(1, (box.clientWidth - 16) / w0));
      box.scrollLeft = 0;
      box.scrollTop = 0;
    }
    function centre(el) {                // the cell `el` at the middle of the view, at its size at least
      if (zoom < 1) { set(1); }
      var b = box.getBoundingClientRect(), r = el.getBoundingClientRect();
      box.scrollLeft += r.left + r.width / 2 - (b.left + box.clientLeft + box.clientWidth / 2);
      box.scrollTop += r.top + r.height / 2 - (b.top + box.clientTop + box.clientHeight / 2);
    }
    var fitted = false;
    function firstFit() {                // a drawing wider than its box starts fitted, once the box is shown
      if (fitted || !box.clientWidth) { return; }
      fitted = true;
      if (w0 > box.clientWidth) { fit(); }
    }
    function show() {                    // open the tab that holds the drawing
      var pane = box.closest("[role='tabpanel']");
      var tab = pane && pane.hidden ? document.getElementById(pane.getAttribute("aria-labelledby")) : null;
      if (tab) { tab.click(); }
      firstFit();
    }
    function pick(el) {                  // mark one cell and bring it (and the box) into view
      show();
      Array.prototype.forEach.call(svg.querySelectorAll(".c.picked"), function (c) { c.classList.remove("picked"); });
      el.classList.add("picked");
      centre(el);
      var b = box.getBoundingClientRect();
      if (b.top < 0 || b.bottom > (window.innerHeight || document.documentElement.clientHeight)) {
        box.scrollIntoView({ block: "center" });
      }
    }
    tools.hidden = false;
    Array.prototype.forEach.call(tools.querySelectorAll("button[data-zoom]"), function (btn) {
      btn.addEventListener("click", function () {
        var how = btn.getAttribute("data-zoom");
        if (how === "fit") { fit(); } else if (how === "one") { set(1); } else { set(zoom * (how === "in" ? 1.25 : 0.8)); }
      });
    });
    var crit = tools.querySelector("input[data-crit]");
    if (crit) {
      crit.addEventListener("change", function () { box.classList.toggle("no-crit", !crit.checked); });
    }
    var find = tools.querySelector("input[data-find]"), count = tools.querySelector("[data-find-count]");
    var cells = Array.prototype.slice.call(svg.querySelectorAll(".c[data-inst]"));
    var hits = [], at = -1;
    if (find && count) {
      find.addEventListener("input", function () {
        var q = find.value.trim().toLowerCase();
        cells.forEach(function (c) { c.classList.remove("hit"); });
        hits = [];
        at = -1;
        if (q) {
          hits = cells.filter(function (c) {
            var t = c.querySelector("title");
            return ((c.getAttribute("data-inst") || "") + " " + (t ? t.textContent : "")).toLowerCase().indexOf(q) >= 0;
          });
          hits.forEach(function (c) { c.classList.add("hit"); });
        }
        count.textContent = !q ? "" : !hits.length ? "no cell" :
          hits.length + (hits.length === 1 ? " cell" : " cells") + " · Enter: the next";
      });
      find.addEventListener("keydown", function (e) {
        if (e.key !== "Enter" || !hits.length) { return; }
        e.preventDefault();
        at = (at + (e.shiftKey ? hits.length - 1 : 1)) % hits.length;
        pick(hits[at]);
        count.textContent = (at + 1) + " of " + hits.length + (hits.length === 1 ? " cell" : " cells");
      });
    }
    function target(href) {
      var el = href && href.charAt(0) === "#" ? document.getElementById(href.slice(1)) : null;
      return el && box.contains(el) ? el : null;
    }
    // in the capture phase: this link is handled here, before site.js's own handling of links into a tab
    document.addEventListener("click", function (e) {
      var a = e.target && e.target.closest ? e.target.closest("a.sch-link") : null;
      var el = a ? target(a.getAttribute("href")) : null;
      if (!el || e.button !== 0 || e.metaKey || e.ctrlKey || e.shiftKey || e.altKey) { return; }
      e.preventDefault();
      if (crit && !crit.checked) { crit.checked = true; box.classList.remove("no-crit"); }
      pick(el);
      if (window.history && history.replaceState) { history.replaceState(null, "", a.getAttribute("href")); }
    }, true);
    firstFit();
    if (!fitted && window.ResizeObserver) {             // in a hidden tab: fitted when the tab opens
      var watch = new ResizeObserver(function () {
        firstFit();
        if (fitted) { watch.disconnect(); }
      });
      watch.observe(box);
    }
    var start = target(location.hash);
    if (start) { pick(start); }
  }

  // -- the explorer ---------------------------------------------------------------------------

  // `scope`: the element holding one explorer and its data (a task page has one per library view, site/build.py `dual`)
  function wireExplorer(data, scope) {
    var controls = scope.querySelector("[data-explorer-controls]");
    var box = scope.querySelector("[data-explorer]");
    if (!controls || !box || !data.metrics || data.metrics.length < 2) { return; }
    var sel = { x: controls.querySelector('select[data-axis="x"]'), y: controls.querySelector('select[data-axis="y"]') };
    var log = { x: controls.querySelector('input[data-log="x"]'), y: controls.querySelector('input[data-log="y"]') };
    var note = scope.querySelector("[data-explorer-note]");
    var pointNote = scope.querySelector("[data-point-note]");
    var scoredNote = pointNote ? pointNote.innerHTML : "";
    var buttons = controls.querySelectorAll("button[data-point]");
    var points = {};
    (data.points || []).forEach(function (p) { points[p.key] = p; });
    var current = null;                  // the measured point drawn (null: the scored point)
    controls.hidden = false;

    function view() {                    // what is drawn: the scored point's ranked designs, or a measured point's
      if (current === null || !data.at || !data.at[current]) { return data; }
      return { task: data.task, metrics: data.metrics, designs: data.at[current], where: points[current].full };
    }

    function values(key) {
      return view().designs.map(function (d) { return d.m[key]; }).filter(function (v) { return v !== undefined; });
    }

    function autoLog(a) {                // a range past 10x on positive values starts on a log axis
      var v = values(sel[a].value), lo = Math.min.apply(null, v), hi = Math.max.apply(null, v);
      log[a].disabled = !(lo > 0);
      log[a].checked = lo > 0 && hi / lo > 10;
    }

    var drawn = null;                  // the size the script last drew at (null: the server's drawings)

    function draw() {
      drawn = box.clientWidth < COMPACT_BELOW ? "compact" : "wide";
      var v = view();
      var r = drawScatter(v, sel.x.value, sel.y.value, log.x.checked, log.y.checked, drawn === "compact");
      var tip = box.querySelector(":scope > .chart-tip");
      box.innerHTML = r.svg || '<p class="empty">No design has both numbers' + (v.where ? " at " + esc(v.where) : "") + ".</p>";
      if (tip) { tip.hidden = true; box.appendChild(tip); }
      if (note) {
        note.textContent = r.n + " of " + v.designs.length + " designs have both numbers" +
          (v.where ? " at " + v.where : "") + (r.n < v.designs.length ? " (the rest lack one)." : ".");
        note.hidden = r.n >= v.designs.length;   // said only when designs are missing from the plot (build.explorer_html)
      }
    }

    function choose(key) {
      var scored = points[key] && points[key].scored;
      current = scored ? null : key;
      Array.prototype.forEach.call(buttons, function (b) {
        b.setAttribute("aria-pressed", b.getAttribute("data-point") === key ? "true" : "false");
      });
      if (pointNote) {
        if (scored) {
          pointNote.innerHTML = scoredNote;
        } else {
          var ranked = (data.points || []).filter(function (p) { return p.scored; })[0];
          pointNote.innerHTML = "<strong>" + esc(points[key].full) + '</strong>: <span class="measured">' + MEASURED +
            "</span>. The same proved " +
            "designs through the same pinned flow at other parameters; " +
            (data.preview ? "this task is a preview, so nothing of it is ranked yet." :
              "the leaderboard ranks at " + esc(ranked ? ranked.full : "the scored point") + " only.");
        }
      }
      autoLog("x"); autoLog("y");
      draw();
    }

    refitOnResize(box, function () { return drawn; }, draw);

    ["x", "y"].forEach(function (a) {
      sel[a].addEventListener("change", function () { autoLog(a); draw(); });
      log[a].addEventListener("change", draw);
      var v = values(sel[a].value);
      log[a].disabled = !(Math.min.apply(null, v) > 0);
    });
    Array.prototype.forEach.call(buttons, function (b) {
      b.addEventListener("click", function () { choose(b.getAttribute("data-point")); });
    });
  }

  // -- the scaling view (svgplot.line_chart) ----------------------------------------------------

  function spread(ys, lo, hi, gap) {   // svgplot._spread: label positions at least `gap` apart in [lo, hi]
    var out = [];
    ys.forEach(function (y) { out.push(out.length ? Math.max(y, out[out.length - 1] + gap) : Math.max(y, lo)); });
    var over = out.length ? out[out.length - 1] - hi : 0;
    if (over > 0) {
      out = out.map(function (y) { return y - over; });
      for (var k = out.length - 2; k >= 0; k--) { out[k] = Math.min(out[k], out[k + 1] - gap); }
    }
    return out;
  }

  function shortName(name, n) { return name.length <= n ? name : name.slice(0, n - 1) + "…"; }

  function lineValues(sc, ln, key, relative) {   // [[point, value]]: the metric, or over par's at the same point
    var base = {};
    if (relative) {
      sc.lines.filter(function (l) { return l.id === sc.par; })[0].pts.forEach(function (p) { base[p.key] = p.m[key]; });
    }
    var out = [];
    ln.pts.forEach(function (p) {
      var v = p.m[key];
      if (v === undefined) { return; }
      if (relative) {
        if (!base[p.key]) { return; }
        v = v / base[p.key];
      }
      out.push([p, v]);
    });
    return out;
  }

  function lineTip(ln) {
    var what = ln.family ? ln.names.length + " sizes of one generator: " + ln.names.join(", ") :
      (ln.names.length > 1 ? "the same numbers at every point: " + ln.names.join(", ") : null);
    var out = [ln.name, KIND_TEXT[ln.kind] + (ln.banned ? " · banned operator" : "") + " · " + MEASURED];
    if (what) { out.push(what); }
    return out;
  }

  function drawLines(data, key, relative, xlog, ylog, compact) {
    var sc = data.scaling, F = compact ? LINE_FRAMES.compact : LINE_FRAMES.wide, W = F.w, H = F.h;
    var byKey = {};
    data.metrics.forEach(function (m) { byKey[m.key] = m; });
    var m = byKey[key];
    var lines = sc.lines.map(function (ln) {
      var vals = lineValues(sc, ln, key, relative);
      return { ln: ln, pts: vals.map(function (pv) {
        var p = pv[0], v = pv[1];
        return { x: p.x, y: v, tip: [ln.name, sc.points[p.key] + (p.key === sc.scored ? " · the scored point" : " · " + MEASURED),
          m.label + ": " + fmtMetric(m, p.m[key]) + (m.unit ? " " + m.unit : "") +
          (relative ? " (×" + v.toFixed(2) + " par)" : "")] };
      }) };
    }).filter(function (l) { return l.pts.length >= 2; });
    if (!lines.length) { return { svg: "", n: 0 }; }
    var left = F.left, right = W - F.right, top = F.top, bottom = H - F.bottom;
    var xv = [], yv = relative ? [1] : [];
    lines.forEach(function (l) { l.pts.forEach(function (p) { xv.push(p.x); yv.push(p.y); }); });
    var xs = new Scale(Math.min.apply(null, xv), Math.max.apply(null, xv), left + 14, right - 14, { log: xlog, integer: !xlog });
    var xticks = sc.ticks.filter(function (t) { return t.x >= xs.lo && t.x <= xs.hi; })
      .sort(function (a, b) { return a.x - b.x; });
    var rows = tickRows(xticks.map(function (t) { return xs.map(t.x); }), xticks.map(function (t) { return t.label; }), F.charW);
    if (rows.some(function (r) { return r > 0; })) { H += 16; }   // a second row of tick labels: the same plot, 16 more below
    var ys = new Scale(Math.min.apply(null, yv), Math.max.apply(null, yv), bottom, top,
                       { log: ylog, integer: !!INTEGER[key] && !relative });
    var yLabel = relative ? m.label + " ÷ par's" : axisLabel(m);
    var xt = sc.x_label + (xs.log ? ", log scale" : ""), yt = yLabel + (ys.log ? ", log scale" : "") + Y_BETTER;
    var title = data.task + ": " + m.label.toLowerCase() + (relative ? " over par" : "") + " against " + sc.x_label +
                ", one line per design";
    var s = ['<svg class="chart lines' + (compact ? " compact" : "") + '" viewBox="0 0 ' + W + " " + H + '" role="img" aria-label="' +
             esc(title) + '" xmlns="http://www.w3.org/2000/svg"><title>' + esc(title) + "</title><desc>" + esc(lines.length +
             " designs, " + yLabel + " (y) against " + sc.x_label + " (x), one line each, named on the right; lower is better.") +
             '</desc><g class="axes">'];
    ys.ticks(F.ticks).forEach(function (v) {
      var y = ys.map(v);
      s.push('<line class="grid" x1="' + f1(left) + '" x2="' + f1(right) + '" y1="' + f1(y) + '" y2="' + f1(y) + '"/>' +
             '<text class="tick" x="' + f1(left - 8) + '" y="' + f1(y + 4) + '" text-anchor="end">' + esc(num(v)) + "</text>");
    });
    xticks.forEach(function (t, k) {
      var x = xs.map(t.x);
      s.push('<line class="grid" x1="' + f1(x) + '" x2="' + f1(x) + '" y1="' + f1(top) + '" y2="' + f1(bottom) + '"/>' +
             '<text class="tick" x="' + f1(x) + '" y="' + f1(bottom + 18 + 16 * rows[k]) + '" text-anchor="middle">' +
             esc(t.label) + "</text>");
    });
    s.push('<line class="axis" x1="' + f1(left) + '" x2="' + f1(right) + '" y1="' + f1(bottom) + '" y2="' + f1(bottom) + '"/>' +
           '<line class="axis" x1="' + f1(left) + '" x2="' + f1(left) + '" y1="' + f1(top) + '" y2="' + f1(bottom) + '"/>' +
           '<text class="axis-title" x="' + f1((left + right) / 2) + '" y="' + f1(H - 8) + '" text-anchor="middle">' + esc(xt) + "</text>" +
           (compact ? '<text class="axis-title" x="4.0" y="' + f1(top - 12) + '" text-anchor="start">' :
            '<text class="axis-title" transform="translate(14 ' + f1((top + bottom) / 2) + ') rotate(-90)" text-anchor="middle">') +
           esc(yt) + "</text></g>");
    if (relative) {
      var gy = ys.map(1);
      s.push('<line class="par-line" x1="' + f1(left) + '" x2="' + f1(right) + '" y1="' + f1(gy) + '" y2="' + f1(gy) + '"></line>');
    }
    var ends = lines.map(function (l) { return [ys.map(l.pts[l.pts.length - 1].y), l.ln.id]; })
      .sort(function (a, b) { return a[0] - b[0] || (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0); });
    var spots = spread(ends.map(function (e) { return e[0]; }), top + 6, bottom - 4, F.gap), spot = {};
    ends.forEach(function (e, k) { spot[e[1]] = spots[k]; });
    var lx = right + 10;
    lines.sort(function (a, b) {
      return (KIND_ORDER[a.ln.kind] - KIND_ORDER[b.ln.kind]) || (a.ln.id < b.ln.id ? -1 : a.ln.id > b.ln.id ? 1 : 0);
    });
    lines.forEach(function (l) {
      var ln = l.ln, cls = { record: "s-record", reference: "s-reference", baseline: "s-baseline" }[ln.kind];
      var tip = lineTip(ln);
      var coords = l.pts.map(function (p) { return f1(xs.map(p.x)) + "," + f1(ys.map(p.y)); }).join(" ");
      var g = '<g class="series" data-line-kind="' + esc(ln.kind) + '" data-id="' + esc(ln.id) + '"><g data-tip="' +
              esc(tip.join("\n")) + '"><polyline class="series-line ' + cls + '" points="' + coords + '"/>' +
              '<polyline class="series-hit" points="' + coords + '"/></g>';
      l.pts.forEach(function (p) {
        var x = xs.map(p.x), y = ys.map(p.y);
        var mk = '<g class="mark" data-line-kind="' + esc(ln.kind) + '" data-x="' + esc(p.x) + '" data-tip="' + esc(p.tip.join("\n")) +
                 '"><circle class="hit" cx="' + f1(x) + '" cy="' + f1(y) + '" r="10"/>' + marker(ln.kind, x, y, ln.banned, 4) + "</g>";
        g += ln.href ? '<a href="' + esc(ln.href) + '" aria-label="' + esc(p.tip[0]) + '">' + mk + "</a>" : mk;
      });
      var last = l.pts[l.pts.length - 1], x = xs.map(last.x), y = ys.map(last.y), ly = spot[ln.id];
      g += '<g class="series-name" data-tip="' + esc(tip.join("\n")) + '"><path class="leader" d="M' + f1(x + 6) + " " + f1(y) +
           "L" + f1(lx - 4) + " " + f1(ly - 4) + '"/><text class="lv-name" x="' + f1(lx) + '" y="' + f1(ly) + '">' +
           esc(shortName(ln.name, F.chars)) + "</text></g></g>";
      s.push(g);
    });
    s.push("</svg>");
    return { svg: s.join(""), n: lines.length };
  }

  // A drawing the script made is redrawn when its box crosses COMPACT_BELOW. The box is watched itself (a
  // ResizeObserver; the window's resize event where there is none), so a box that is hidden (the other library's
  // view, a closed tab) is not redrawn at width 0, and is redrawn at its own width once it is shown again.
  function refitOnResize(box, drawnAs, draw) {
    var pending = null;
    function refit() {
      if (drawnAs() === null || !box.clientWidth) { return; }   // the server's drawing, or hidden: nothing to fit
      clearTimeout(pending);
      pending = setTimeout(function () {
        var w = box.clientWidth;
        if (w && (w < COMPACT_BELOW ? "compact" : "wide") !== drawnAs()) { draw(); }
      }, 150);
    }
    if (window.ResizeObserver) {
      new ResizeObserver(refit).observe(box);
    } else {
      window.addEventListener("resize", refit);
    }
  }

  function wireScaling(data) {
    var sc = data.scaling;
    var controls = document.querySelector("[data-scaling-controls]");
    var box = document.querySelector("[data-scaling]");
    if (!sc || !controls || !box) { return; }
    var metric = controls.querySelector("select[data-scaling-metric]");
    var rel = controls.querySelector("input[data-scaling-relative]");
    var log = { x: controls.querySelector('input[data-scaling-log="x"]'), y: controls.querySelector('input[data-scaling-log="y"]') };
    var note = document.querySelector("[data-scaling-note]");
    var figure = box.closest("figure");
    var byKey = {};
    data.metrics.forEach(function (m) { byKey[m.key] = m; });
    controls.hidden = false;
    var drawn = null;

    function draw() {
      drawn = box.clientWidth < COMPACT_BELOW ? "compact" : "wide";
      var relative = !!(rel && rel.checked && sc.par);
      var r = drawLines(data, metric.value, relative, log.x.checked, log.y.checked, drawn === "compact");
      var tip = box.querySelector(":scope > .chart-tip");
      box.innerHTML = r.svg || '<p class="empty">No design has this number at two points or more.</p>';
      if (tip) { tip.hidden = true; box.appendChild(tip); }
      var parIcon = figure ? figure.querySelector("ul.legend .par-line") : null;
      if (parIcon && parIcon.closest("li")) { parIcon.closest("li").hidden = !relative; }
      if (note) {                        // the server's sentence (build.scaling_html), par's name as code
        var m = byKey[metric.value];
        note.innerHTML = relative ? esc(m.label) + " of each design over par's (<code>" + esc(sc.par_name) +
          "</code>) at the same point, against " + esc(sc.x_label) + ": 1 is par, and a line under it beats par at " +
          "that size, so where two lines cross one design starts to pay off against the other." :
          esc(m.label) + " of each design against " + esc(sc.x_label) + ".";
      }
    }

    metric.addEventListener("change", draw);
    if (rel) { rel.addEventListener("change", draw); }
    log.x.addEventListener("change", draw);
    log.y.addEventListener("change", draw);
    refitOnResize(box, function () { return drawn; }, draw);
  }

  function init() {
    Array.prototype.forEach.call(document.querySelectorAll(".chart-box"), function (box) {
      dropTitles(box);
      wireTips(box);
    });
    Array.prototype.forEach.call(document.querySelectorAll("[data-scale-toggle]"), wireScale);
    Array.prototype.forEach.call(document.querySelectorAll("[data-view-toggle]"), wireViewToggle);
    Array.prototype.forEach.call(document.querySelectorAll("[data-schematic]"), wireSchematic);
    // the page's data: #task-data (sky130, with the scaling view's) and #task-data-asap7 (the ASAP7 view's explorer),
    // each beside the explorer it feeds
    Array.prototype.forEach.call(document.querySelectorAll('script[type="application/json"][id^="task-data"]'), function (el) {
      var data = null;
      try { data = JSON.parse(el.textContent); } catch (e) { /* the server's drawings stay */ }
      if (data) {
        try { wireExplorer(data, el.parentNode || document); } catch (e) { /* the server's drawing stays */ }
        if (data.scaling) {
          try { wireScaling(data); } catch (e) { /* the server's drawing stays */ }
        }
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
