// site/charts.js's Size view of the explorer, outside a browser (no DOM, no libraries): the line names at the right
// edge (decided 2026-11-13: the submission's short title, its writeup's first line, in place of the player's name;
// par's line "par · <title>"; two lines with the same title get the player's name appended; a name longer than the
// margin cut with an ellipsis, in the middle when two cut names would read the same; the player's name in the
// tooltip), their spacing in the wide drawing (no two names closer than the frame's gap, every name inside the
// drawing), and the phone drawing (compact: no names, the tooltips name each line).
//     node tests/site/chartsjs_sizes_check.js site/charts.js DATA.json ...   (test_sizes runs it when node is installed)
// Each DATA.json is a task page's explorer data (#task-data). The script is loaded with a stub document that is
// still "loading", so nothing is wired; its functions are reached through one line added before its closing `})();`.
const fs = require("fs");
const src = fs.readFileSync(process.argv[2], "utf8");
const end = src.lastIndexOf("})();");
const code = src.slice(0, end) + "globalThis.__charts = { sizeLabels, sizeLinesOf, drawLines, LINE_FRAMES };\n" +
  src.slice(end);
globalThis.document = { readyState: "loading", addEventListener() {} };
new Function(code)();
const C = globalThis.__charts;
let fails = 0, oks = 0;
function ok(c, msg) { if (!c) { fails++; console.log("FAIL " + msg); } else { oks++; } }

// -- the naming rule on made-up lines ----------------------------------------------------------------------------
function line(id, title, name, extra) {
  return Object.assign({ id, title, names: [name], par: false, kind: "record" }, extra || {});
}
const n = C.LINE_FRAMES.wide.chars;
let got = C.sizeLabels([line("a", "Wallace tree", "ferngold"), line("b", "Dadda tree", "slatecairn")], n);
ok(JSON.stringify(got) === JSON.stringify(["Wallace tree", "Dadda tree"]), "titles, not players: " + got);
got = C.sizeLabels([line("a", "Wallace tree", "ferngold"), line("b", "Wallace tree", "slatecairn"),
                    line("c", "Booth", "x")], n);
ok(got[0] === "Wallace tree · ferngold" && got[1] === "Wallace tree · slatecairn" && got[2] === "Booth",
   "the same title: the player appended: " + got);
got = C.sizeLabels([line("p", null, "mul_n", { par: true, names: ["mul_n", "mul_n_byhand"], kind: "reference" }),
                    line("q", "N² multiply-accumulate units, one step counter", "matmul_g1", { par: true })], n);
ok(got[0] === "par · mul_n +1", "par's line keeps its prefix and +N: " + got[0]);
ok(got[1].startsWith("par · N² multiply") && got[1].endsWith("…") && got[1].length === n, "cut to fit: " + got[1]);
got = C.sizeLabels([line("a", "Weight-FIFO systolic array, uncleared PE registers", "heron"),
                    line("b", "Weight-FIFO systolic array, cleared on start", "heron")], n);
ok(got[0] !== got[1] && got.every(function (l) { return l.length <= n && l.indexOf("…") > 0; }) &&
   got[0].endsWith("PE registers") && got[1].endsWith("ed on start"), "two cut names that read the same: cut in the " +
   "middle: " + got);
got = C.sizeLabels([line("a", "A very long title that does not fit in the margin at all", "longplayername"),
                    line("b", "A very long title that does not fit in the margin at all", "other")], n);
ok(got[0].endsWith(" · longplayername") && got[1].endsWith(" · other") && got.every(function (l) { return l.length <= n; }),
   "the player's name kept whole when the title is cut: " + got);
got = C.sizeLabels([line("a", null, "yosys_mul", { kind: "baseline" })], n);
ok(got[0] === "yosys_mul", "a design without a title: its name: " + got);

// -- every task's Size view, drawn ----------------------------------------------------------------------------------
function texts(svg, cls) {
  const re = new RegExp('<text class="' + cls + '" x="([-0-9.]+)" y="([-0-9.]+)">([^<]*)</text>', "g");
  const out = [];
  let m;
  while ((m = re.exec(svg))) { out.push({ x: Number(m[1]), y: Number(m[2]), t: m[3] }); }
  return out;
}
function unesc(s) { return s.replace(/&quot;/g, '"').replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&"); }
let views = 0;
for (const path of process.argv.slice(3)) {
  const data = JSON.parse(fs.readFileSync(path, "utf8"));
  (data.sizes || []).forEach(function (ax, i) {
    const metric = data.metrics.some(function (m) { return m.key === "adp"; }) ? "adp" : data.metrics[0].key;
    [false, true].forEach(function (relative) {
      const sc = C.sizeLinesOf(data, ax, metric);
      if (relative && !sc.par) { return; }
      const where = data.task + " size axis " + i + (relative ? " ÷ par" : "");
      const wide = C.drawLines(data, sc, metric, relative, true, true, false);
      if (!wide.svg) { return; }
      views++;
      const F = C.LINE_FRAMES.wide;
      const W = Number(/viewBox="0 0 ([0-9.]+) ([0-9.]+)"/.exec(wide.svg)[1]);
      const H = Number(/viewBox="0 0 ([0-9.]+) ([0-9.]+)"/.exec(wide.svg)[2]);
      const names = texts(wide.svg, "lv-name");
      ok(names.length === wide.n, where + ": one name per line drawn (" + names.length + " of " + wide.n + ")");
      const drawn = sc.lines.filter(function (ln) {
        return new RegExp('data-id="' + ln.id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + '"').test(wide.svg);
      });
      const want = C.sizeLabels(drawn, F.chars);
      const labels = names.map(function (x) { return unesc(x.t); });
      ok(JSON.stringify(labels.slice().sort()) === JSON.stringify(want.slice().sort()), where + ": the names are " +
         "sizeLabels' of the lines drawn");
      ok(new Set(labels).size === labels.length, where + ": no two names alike: " + labels.join(" | "));
      drawn.forEach(function (ln) {
        const lab = want[drawn.indexOf(ln)];
        const player = ln.names[0];
        if (ln.title) {
          ok(lab.indexOf(ln.title.slice(0, 6)) >= 0, where + ": " + player + "'s line named by its title: " + lab);
          const dup = drawn.filter(function (o) { return o.title === ln.title; }).length > 1;
          ok(dup === (lab.indexOf(" · " + player) >= 0), where + ": the player in the name only for a shared title: " +
             lab);
        }
        ok(!ln.par || lab.indexOf("par · ") === 0, where + ": par's line named par · <title>: " + lab);
        const g = new RegExp('data-id="' + ln.id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + '"><g data-tip="([^"]*)"')
          .exec(wide.svg);
        ok(g && unesc(g[1]).indexOf(player) >= 0, where + ": the player's name in the line's tooltip (" + player + ")");
      });
      const ys = names.map(function (x) { return x.y; }).sort(function (a, b) { return a - b; });
      ok(ys.every(function (y, k) { return k === 0 || y - ys[k - 1] >= F.gap - 0.11; }), where + ": names at least " +
         F.gap + " apart (font 11): " + ys.join(","));
      ok(names.every(function (x) { return x.y - 9 >= 0 && x.y <= H && x.x + unesc(x.t).length * F.charW <= W; }),
         where + ": every name inside the drawing");
      const phone = C.drawLines(data, sc, metric, relative, true, true, true);
      ok(texts(phone.svg, "lv-name").length === 0 && phone.svg.indexOf('class="series-name"') < 0,
         where + ": on a phone no names at the right edge");
      ok(phone.svg.indexOf("named in its tooltip") > 0, where + ": the phone drawing says the tooltips name the lines");
      ok((phone.svg.match(/<g class="series" /g) || []).length === phone.n && phone.n === wide.n,
         where + ": the phone drawing keeps every line");
      drawn.forEach(function (ln) {
        const g = new RegExp('data-id="' + ln.id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&") + '"><g data-tip="([^"]*)"')
          .exec(phone.svg);
        ok(g && unesc(g[1]).indexOf(ln.names[0]) >= 0 && (!ln.title || unesc(g[1]).indexOf(ln.title) === 0),
           where + ": on a phone the tooltip names the line by title and player (" + ln.names[0] + ")");
      });
    });
  });
}
ok(views > 0 || process.argv.length === 3, "some Size view drawn");
console.log(`chartsjs_sizes_check: ${oks} ok, ${fails} failed, ${views} views`);
process.exit(fails ? 1 : 0);
