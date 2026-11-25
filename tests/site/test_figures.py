"""The figures of the writeups (decided 2026-11-16, site/figs): the figure block, the generators, and each figure
checked against its design.

    python3.12 svgolf/tests/site/test_figures.py

THE CHECKS AGAINST THE DESIGNS. A figure is drawn from a model that restates its design's index formulas; these
tests compare every model with the design itself:
  * combinational figures (add, mul, clmul): the design is elaborated by Yosys at the drawn size (read_verilog -sv,
    hierarchy -chparam, proc, opt_clean: no synthesis, so each assign is still its own cells), and for every signal
    bit the figure draws, the set of named signal bits its gates read (`Netlist.reads`) must be the model's, a
    pass-through the same net;
  * clocked figures (sorter, arbiter, matmul): the design is simulated by Icarus Verilog on the figure's own inputs
    (matmul: random matrices at the scoring point), and every value the figure shows, edge by edge, must be the
    simulation's;
  * fdivp: Yosys `eval` of the SRT design's own threshold and comparison nets for every divisor column and estimate,
    and the arithmetic cells of both cores' elaborated netlists.
Those tests skip without yosys, iverilog and vvp (as test_schematics.py does without its tools); the rest needs no
tool: the figure block, determinism, the registry against the records, and a property of each model.
"""

import contextlib
import io
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
DATA = os.path.join(SVGOLF, "leaderboard", "data")
WRITEUPS = os.path.join(SVGOLF, "leaderboard", "writeups")
sys.path.insert(0, SITE)
sys.dont_write_bytecode = True

import figs                                        # noqa: E402
import html                                        # noqa: E402
import md                                          # noqa: E402
import safehtml                                    # noqa: E402
import writeup                                     # noqa: E402
from figs import adders, clmul, clocked, divider, matmul, multipliers   # noqa: E402


def records():
    out = []
    for task in sorted(os.listdir(DATA)):
        d = os.path.join(DATA, task)
        if not os.path.isdir(d):
            continue
        for name in sorted(os.listdir(d)):
            if name.endswith(".json"):
                with open(os.path.join(d, name), encoding="utf-8") as fh:
                    out.append(json.load(fh))
    return out


RECORDS = records()


def design_path(sha):
    """The design file (in leaderboard/data/) whose sha256 is `sha`."""
    for r in RECORDS:
        if r["files"]["sv"]["sha256"] == sha:
            return os.path.join(DATA, r["task"], r["record_hash"] + ".sv")
    raise KeyError(sha)


def point(text):
    """{"N": 16} of "N = 16"; {"N": 4, "W": 8, "AccW": 32} of "N = 4, W = 8, AccW = 32"."""
    return {k: int(v) for k, v in re.findall(r"(\w+) = (\d+)", text)}


def missing(*exes):
    gone = [e for e in exes if not (yosys_cmd() if e == "yosys" else shutil.which(e))]
    return f"needs {', '.join(gone)}" if gone else ""


_YOSYS = []


def yosys_cmd():
    """The flow's Yosys as score.py runs it (the rating build, score/yosys_wasm.py, unless $SVGOLF_YOSYS names
    another), or None where it cannot run."""
    if not _YOSYS:
        sys.path.insert(0, os.path.join(SVGOLF, "score"))
        import score
        _YOSYS.append(None if score.yosys_missing() else score.yosys_argv(score.yosys_bin()))
    return _YOSYS[0]


def block(name, alt="Alt text.", caption="A caption."):
    """A writeup's figure the site draws (HTML since 2026-11-16): `alt` plain text, `caption` HTML."""
    return f'<figure data-figure="{name}" data-alt="{html.escape(alt)}">\n<figcaption>{caption}</figcaption>\n</figure>'


FIGURE_NAME = re.compile(r'<figure data-figure="([^"]+)"')


# ---------------------------------------------------------------------------------------------------------------
# the figure block and the registry (no tools)

class FigureBlockTest(unittest.TestCase):
    def render(self, body, **kw):
        return writeup.render(f"<h1>T</h1>\n\n<p>Text.</p>\n\n{body}\n", source="w.html", **kw)[1]

    def test_a_block_is_a_figure_with_its_caption_and_credit(self):
        fig = figs.get("add-kogge-stone")
        h = self.render(block("add-kogge-stone", "The graph & its <nodes>.", 'Every carry, <code>g</code> and <a href='
                              '"https://example.org/x">a link</a>.'), design_sha256=fig.designs[0],
                        rules_href="../../../rules.html#f")
        self.assertRegex(h, r'<figure class="wfig" id="writeup-figure-1"><div class="wfig-box"><svg class="wfig-svg" ')
        self.assertIn('<title id="writeup-figure-1-t">The graph &amp; its &lt;nodes&gt;.</title>', h)
        self.assertIn('aria-labelledby="writeup-figure-1-t writeup-figure-1-d"', h)
        self.assertIn('<span class="wfig-n">Figure 1.</span> Every carry, <code>g</code> and '
                      '<a rel="nofollow ugc noopener" href="https://example.org/x">a link</a>.', h)
        self.assertIn("Drawn at N = 8; the record is scored at N = 16. Figure by the maintainers, generated from the "
                      'design (<a href="../../../rules.html#f">how</a>).</span></figcaption></figure>', h)

    def test_figures_are_numbered_and_ids_stay_unique(self):
        h = self.render("<h2>Figure 1</h2>\n\n" + block("add-ripple") + "\n\n" + block("add-ripple"))
        ids = re.findall(r'\bid="([^"]+)"', h)
        self.assertEqual(len(ids), len(set(ids)), ids)
        self.assertEqual(h.count('<span class="wfig-n">Figure 2.</span>'), 1)

    def test_what_a_block_refuses(self):
        good = figs.get("add-kogge-stone").designs[0]
        ks = "add-kogge-stone"
        for body, why in ((block("no-such-figure"), "no figure is named"),
                          (f'<figure data-figure="{ks}" data-alt="a"></figure>', "holds one <figcaption>"),
                          (f'<figure data-figure="{ks}"><figcaption>c</figcaption></figure>', "both data-figure"),
                          (f'<figure data-figure="{ks}" data-alt="a" src="x.svg"><figcaption>c</figcaption></figure>',
                           "the attribute src is not allowed"),
                          (f'<figure data-figure="{ks}" data-figure="{ks}" data-alt="a"><figcaption>c</figcaption>'
                           "</figure>", "twice"),
                          (f'<figure data-figure="{ks}" data-alt="a"><svg onload=alert(1)></svg><figcaption>c'
                           "</figcaption></figure>", "the attribute onload is not allowed"),
                          (block(ks, caption="x" * 301), "over 300"),
                          (block(ks, alt="x" * 301), "over 300"),
                          (block(ks, caption='<img src="https://example.org/i.png">'), "<img> is not allowed")):
            with self.subTest(why=why):
                with self.assertRaisesRegex(safehtml.HtmlError, re.escape(why)):
                    self.render(body, design_sha256=good)
        with self.assertRaisesRegex(safehtml.HtmlError, "another design"):
            self.render(block("add-ripple"), design_sha256=good)          # the Kogge-Stone record: not its figure

    def test_nothing_a_writer_types_becomes_markup(self):
        h = self.render(block("add-ripple", alt='"><script>alert(1)</script>', caption="&lt;img src=x onerror=y&gt; "
                              "[x](javascript:alert(1))"))
        self.assertNotIn("<script", h)
        self.assertNotIn("<img", h)
        self.assertIn("<title id=\"writeup-figure-1-t\">&quot;&gt;&lt;script&gt;alert(1)&lt;/script&gt;</title>", h)
        self.assertNotRegex(h, r"<[^>]*\son[a-z]+=")

    def test_outside_a_writeup_the_fence_is_code(self):
        h = md.render("```figure\nname: add-ripple\nalt: a\ncaption: c\n```").html
        self.assertIn('<pre class="code" data-lang="figure">', h)
        self.assertNotIn("<svg", h)

    def test_leaderboard_verify_reads_the_block(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location("svgolf_leaderboard_figs",
                                                      os.path.join(SVGOLF, "leaderboard", "leaderboard.py"))
        lb = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(lb)
        render = lb.writeup_renderer()
        rec = RECORDS[0]["record_hash"]
        good = f"<h1>T</h1>\n\n{block('add-ripple')}\n".encode()
        bad = f"<h1>T</h1>\n\n{block('nope')}\n".encode()
        self.assertEqual(lb.writeup_problems(rec + ".html", good, {rec}, (), render), [])
        self.assertTrue(any("line 3: no figure is named" in p
                            for p in lb.writeup_problems(rec + ".html", bad, {rec}, (), render)))

    def test_a_drawn_and_a_generated_figure_in_one_writeup(self):
        """A writer's own drawing and a generated figure are numbered together; only the generated one carries the
        line "Figure by the maintainers, generated from the design"."""
        fig = figs.get("add-kogge-stone")
        own = ('<figure>\n<svg viewBox="0 0 100 40"><title>A box.</title><rect class="b" x="1" y="1" width="20" '
               'height="10"/></svg>\n<figcaption>Hand-drawn by the writer.</figcaption>\n</figure>')
        h = self.render(own + "\n\n" + block("add-kogge-stone"), design_sha256=fig.designs[0])
        first, second = h.split('<figure class="wfig"')[1:]
        self.assertIn('<span class="wfig-n">Figure 1.</span> Hand-drawn by the writer.</figcaption>', first)
        self.assertNotIn("generated from the design", first)
        self.assertIn('<span class="wfig-n">Figure 2.</span>', second)
        self.assertIn("Figure by the maintainers, generated from the design", second)


SAFE_TAGS = {"svg", "title", "desc", "g", "line", "path", "polyline", "polygon", "circle", "rect", "text"}


class RegistryTest(unittest.TestCase):
    def test_each_figure_names_record_designs_of_its_task_and_their_scoring_point(self):
        by_sha = {}
        for r in RECORDS:
            by_sha.setdefault(r["files"]["sv"]["sha256"], []).append(r)
        for name, fig in sorted(figs.REGISTRY.items()):
            with self.subTest(figure=name):
                self.assertTrue(fig.designs)
                for sha in fig.designs:
                    self.assertIn(sha, by_sha, "a design of no record")
                    for r in by_sha[sha]:
                        self.assertEqual(r["task"], fig.task)
                        self.assertEqual(point(fig.scored_at), r["score"]["scoring_point"])
                self.assertEqual(fig.by, "the maintainers")

    def test_generators_are_deterministic_and_draw_only_plain_svg(self):
        for name, fig in sorted(figs.REGISTRY.items()):
            with self.subTest(figure=name):
                a = figs.svg_of(fig, alt="a", uid="u")
                b = figs.svg_of(fig, alt="a", uid="u")
                self.assertEqual(a, b)
                self.assertLessEqual(set(re.findall(r"<([a-zA-Z][a-zA-Z0-9]*)", a)), SAFE_TAGS)
                self.assertNotRegex(a, r"\s(on[a-z]+|href|xlink:href|src)=")
                self.assertEqual(re.findall(r'style="([^"]*)"', a)[0],
                                 re.match(r'.*?(max-width:[0-9.]+px;min-width:[0-9.]+px)', a).group(1))
                self.assertEqual(len(re.findall(r'style="', a)), 1)
                self.assertNotRegex(a, r"#[0-9a-fA-F]{3,6}\b|rgb\(")        # no colour: the classes carry them
                desc = re.search(r"<desc[^>]*>(.*?)</desc>", a).group(1)
                self.assertGreater(len(desc), 100)
                w = float(re.search(r'viewBox="0 0 ([0-9.]+) ', a).group(1))
                self.assertLessEqual(w, 760)

    def test_every_writeup_figure_is_its_records(self):
        by_hash = {r["record_hash"]: r for r in RECORDS}
        for name in sorted(os.listdir(WRITEUPS)):
            if not name.endswith(".html") or name == "TEMPLATE.html":
                continue
            with open(os.path.join(WRITEUPS, name), encoding="utf-8") as fh:
                text = fh.read()
            rec = by_hash[name[:-5]]
            for m in FIGURE_NAME.finditer(text):
                with self.subTest(writeup=name[:12], figure=m.group(1)):
                    self.assertIn(rec["files"]["sv"]["sha256"], figs.get(m.group(1)).designs)
            writeup.render(text, source=name, design_sha256=rec["files"]["sv"]["sha256"])

    def test_every_record_of_a_drawn_design_shows_its_figure(self):
        """No figure is left unused: each record whose design a figure is drawn from shows one of that design's
        figures in its writeup (the coverage of this round: every frontier record and par of add, mul, clmul, fdivp,
        matmul, sorter and arbiter)."""
        shown = {}
        for name in sorted(os.listdir(WRITEUPS)):
            if name.endswith(".html") and name != "TEMPLATE.html":
                with open(os.path.join(WRITEUPS, name), encoding="utf-8") as fh:
                    shown[name[:-5]] = set(FIGURE_NAME.findall(fh.read()))
        drawn = {}
        for fig in figs.REGISTRY.values():
            for sha in fig.designs:
                drawn.setdefault(sha, set()).add(fig.name)
        covered = 0
        for r in RECORDS:
            sha = r["files"]["sv"]["sha256"]
            if sha in drawn:
                with self.subTest(record=r["record_hash"][:12]):
                    self.assertTrue(shown.get(r["record_hash"], set()) & drawn[sha])
                    covered += 1
        self.assertGreaterEqual(covered, 24)


# ---------------------------------------------------------------------------------------------------------------
# a property of each model (no tools)

def clmul_int(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a, b = a << 1, b >> 1
    return r


class ModelTest(unittest.TestCase):
    def test_prefix_graphs_compute_every_carry(self):
        rnd = random.Random(1)
        for model in (adders.kogge_stone, adders.sklansky, adders.ripple):
            for n in (1, 2, 5, 8, 16):
                levels, nodes = model(n)
                cases = ([(a, b, c) for a in range(1 << n) for b in range(1 << n) for c in (0, 1)] if n <= 5 else
                         [(rnd.getrandbits(n), rnd.getrandbits(n), rnd.getrandbits(1)) for _ in range(400)])
                for a, b, c in cases:
                    g = adders.carries(n, levels, nodes, a, b, c)
                    want = [((a & ((1 << k) - 1)) + (b & ((1 << k) - 1)) + c) >> k for k in range(n + 1)]
                    self.assertEqual(g, want, (model.__name__, n, a, b, c))

    def test_the_drawn_node_counts(self):
        self.assertEqual(len(adders.kogge_stone(8)[1]), 21)
        self.assertEqual(len(adders.sklansky(8)[1]), 13)
        self.assertEqual(adders.carry_select(16), ([(0, 0, 5), (1, 6, 11)], (12, 15)))

    def test_the_heap_takes_every_row_once_and_is_a_binary_tree(self):
        for n in (2, 3, 7, 8, 16):
            h, leaves, inner = multipliers.heap(n)
            rows = sorted(r for pair in leaves.values() for r in pair)
            self.assertEqual(rows, list(range(2 * h)))
            kids = sorted(c for pair in inner.values() for c in pair)
            self.assertEqual(kids, list(range(1, 2 * h - 1)))

    def test_the_dadda_stages_add_up(self):
        for n in (2, 3, 5, 8, 16, 33):
            h0, stages = multipliers.dadda(n)
            for st in stages:
                for k in range(2 * n):
                    f, h = st["adders"][k]
                    cin = sum(st["adders"][k - 1]) if k else 0
                    self.assertEqual(st["after"][k], st["before"][k] - 2 * f - h + cin, (n, st["t"], k))
                    self.assertLessEqual(st["after"][k], st["t"])
                    self.assertLessEqual(3 * f + 2 * h, st["before"][k])
            self.assertLessEqual(max(stages[-1]["after"]) if stages else max(h0), 2)
        h0, stages = multipliers.dadda(8)
        self.assertEqual(([s["t"] for s in stages], sum(f for s in stages for f, _ in s["adders"]),
                          sum(h for s in stages for _, h in s["adders"])), ([6, 4, 3, 2], 35, 7))

    def test_the_array_chain(self):
        for n in (3, 8, 16):
            path = multipliers.longest_path(multipliers.array(n))
            self.assertEqual(len(path), n + 2 * (n - 2))
            ins = multipliers.array(n)
            for a, b in zip(path, path[1:]):
                self.assertIn(a, ins[b])

    def test_the_clmul_trees_are_trees_on_their_leaves(self):
        for n in range(1, 21):
            nodes = clmul.tree(n)
            used = sorted(c for pair in nodes.values() for c in pair)
            self.assertEqual(used, list(range(2 * n - 2)))                   # every position but the root, once
            self.assertEqual(max(clmul.tree_depths(n).values()), (n - 1).bit_length())

    def test_the_karatsuba_figures_multiply(self):
        rnd = random.Random(2)
        n = 16
        h, terms = clmul.karatsuba1(n)
        for _ in range(200):
            a, b = rnd.getrandbits(n), rnd.getrandbits(n)
            al, ah, bl, bh = a & ((1 << h) - 1), a >> h, b & ((1 << h) - 1), b >> h
            prod = {"L": clmul_int(al, bl), "H": clmul_int(ah, bh), "M": clmul_int(al ^ ah, bl ^ bh)}
            got = 0
            for i, ts in terms.items():
                bit = 0
                for arr, c in ts:
                    bit ^= (prod[arr] >> c) & 1
                got |= bit << i
            self.assertEqual(got, clmul_int(a, b))
        levels, p, nodes = clmul.karatsuba_tree(n)
        self.assertEqual((levels, p, sum(1 for (l, _) in nodes if l == levels)), (2, 16, 9))

        def node_operands(l, t, a):
            if l == 0:
                return a
            half = p >> l
            parent = node_operands(l - 1, t // 3, a)
            lo, hi = parent & ((1 << half) - 1), parent >> half
            return (lo, hi, lo ^ hi)[t % 3]

        def product(l, t, a, b):
            if l == levels:
                return clmul_int(node_operands(l, t, a), node_operands(l, t, b))
            m = p >> (l + 1)
            lo, hi, mid = (product(l + 1, 3 * t + c, a, b) for c in range(3))
            return lo ^ ((mid ^ lo ^ hi) << m) ^ (hi << 2 * m)
        for _ in range(50):
            a, b = rnd.getrandbits(n), rnd.getrandbits(n)
            self.assertEqual(product(0, 0, a, b), clmul_int(a, b))

    def test_the_sorter_sorts_and_the_arbiter_is_fair(self):
        rows = clocked.sorter_run(clocked.SORTER_N, clocked.SORTER_INPUTS, clocked.SORTER_EDGES)
        self.assertEqual([s["od"] for s in rows if s["ov"]], sorted(clocked.SORTER_INPUTS))
        rows = clocked.arbiter_run(clocked.ARB_N, clocked.ARB_REQS)
        for s in rows:
            self.assertEqual(s["gnt"] & ~s["req"], 0)                        # only a requester
            self.assertLessEqual(bin(s["gnt"]).count("1"), 1)                 # at most one
            self.assertEqual(bool(s["gnt"]), bool(s["req"]))                 # someone, when anyone asks
        self.assertEqual([s["gnt"] for s in rows[:5]], [1, 2, 4, 8, 1])

    def test_what_the_tables_mark_follows_from_their_values(self):
        # the sorter: a cell marked "took the input" holds it, "took the cell above" the old value above (0 at the top)
        rows = clocked.sorter_run(clocked.SORTER_N, clocked.SORTER_INPUTS, clocked.SORTER_EDGES)
        old = [0] * clocked.SORTER_N
        for s in rows:
            for k, how in enumerate(s["how"]):
                above = old[k + 1] if k + 1 < len(old) else 0
                want = {"in": s["in"], "down": above, "hold": old[k]}[how]
                self.assertEqual(s["cells"][k], want)
            old = s["cells"]
        # matmul: the steps read in a cycle are the steps C (or P) gains on its edge
        for v in ("g1", "two", "four", "free", "reg"):
            prev = []
            for s in matmul.schedule(v):
                gained = sorted(set(s["P"] if v == "reg" else s["C"]) - (set() if v == "reg" else set(prev)))
                self.assertEqual(s["read"], gained, (v, s["edge"]))
                prev = s["C"]

    def test_the_matmul_schedules(self):
        lat = {"g1": 4, "two": 2, "four": 1, "free": 4, "reg": 5}
        for v, want in lat.items():
            rows = matmul.schedule(v)
            self.assertEqual(next(s["edge"] for s in rows if s["done"]), want, v)
            self.assertEqual(rows[-1]["C"], [0, 1, 2, 3], v)
        levels, names, table, into_c, done = matmul.pipeline()
        self.assertEqual(sorted(into_c.values()), list(range(16)))
        self.assertEqual((levels, done), (2, 20))

    def test_the_srt_regions_and_the_cores(self):
        for da in range(8):
            ts = [divider.THRESHOLDS[q][da] for q in (2, 1, 0, -1)]
            self.assertEqual(ts, sorted(ts, reverse=True))
            self.assertEqual(len(set(ts)), 4)
        self.assertEqual(divider.cores(11), {"restoring": (13, 12), "srt": (7, 8, 17)})


# ---------------------------------------------------------------------------------------------------------------
# the checks against the designs: Yosys

class Netlist:
    """A design elaborated by Yosys (no synthesis): which named signal bits each signal bit's gates read."""

    def __init__(self, path, top, params, tmp):
        out = os.path.join(tmp, "n.json")
        chp = " ".join(f"-chparam {k} {v}" for k, v in params.items())
        subprocess.run(yosys_cmd() + ["-q", "-p", f"read_verilog -sv {path}; hierarchy -top {top} {chp}; proc -noopt; "
                        f"opt_clean; write_json {out}"], check=True, capture_output=True)
        with open(out, encoding="utf-8") as fh:
            mod = json.load(fh)["modules"][top]
        self.names = {k: v["bits"] for k, v in mod["netnames"].items()}
        self.named = {b for k, v in mod["netnames"].items() if not v.get("hide_name") for b in v["bits"]
                      if isinstance(b, int)}
        self.driver = {}                            # net -> (cell, output port, bit position)
        for c in mod["cells"].values():
            for port, way in c["port_directions"].items():
                if way == "output":
                    for k, b in enumerate(c["connections"][port]):
                        self.driver[b] = (c, k)
        self.cells = list(mod["cells"].values())

    def net(self, name, i=0):
        return self.names[name][i]

    BITWISE = {"$and", "$or", "$xor", "$xnor", "$not", "$pos", "$buf"}

    @staticmethod
    def _bit(c, port, k):
        """Input `port`'s bit that output bit k of a bitwise cell reads (extended as Yosys extends it)."""
        bits = c["connections"][port]
        if k < len(bits):
            return [bits[k]]
        signed = int(c["parameters"].get(f"{port}_SIGNED", "0"), 2)
        return [bits[-1]] if signed and bits else []

    def inputs(self, x):
        """The input nets output net x's value depends on: bit by bit for a bitwise cell or a mux, else every
        input bit of the cell."""
        c, k = self.driver[x]
        t = c["type"]
        if t in self.BITWISE:
            return [y for p in ("A", "B") if p in c["connections"] for y in self._bit(c, p, k)]
        if t == "$mux":
            return [c["connections"]["A"][k], c["connections"]["B"][k]] + c["connections"]["S"]
        return [y for p, way in c["port_directions"].items() if way == "input" for y in c["connections"][p]]

    def reads(self, b, stop=None):
        """The nets (ints) at which the cone of net b stops: named nets (or `stop`), never constants."""
        stop = self.named if stop is None else stop
        out, seen, todo = set(), set(), [b]
        while todo:
            x = todo.pop()
            if x not in self.driver:
                out.add(x)
                continue
            for y in self.inputs(x):
                if not isinstance(y, int) or y in seen:
                    continue
                seen.add(y)
                (out.add if y in stop and y != b else todo.append)(y)
        return out

    def same(self, b, want):
        """True when net b is what `want` (a set of nets) says: the one net it names (an assign), or a cell reading
        exactly those nets."""
        return (len(want) == 1 and b in want) or self.reads(b) == want


def nets(nl, pairs):
    """The nets of [(name, bit)], constants dropped."""
    return {nl.net(n, i) for n, i in pairs if isinstance(nl.net(n, i), int)}


@unittest.skipIf(missing("yosys"), missing("yosys"))
class YosysTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def elab(self, sha, top, **params):
        return Netlist(design_path(sha), top, params, self.tmp.name)

    def check_prefix(self, sha, model, n):
        nl = self.elab(sha, "add_n", N=n)
        levels, nodes = model(n)
        at = {(l, i): j for l, i, j in nodes}
        g = lambda l, i: ("g", l * (n + 1) + i)            # noqa: E731
        p = lambda l, i: ("p", l * (n + 1) + i)            # noqa: E731
        for l in range(levels):
            for i in range(n + 1):
                with self.subTest(level=l, position=i):
                    out = nl.net(*g(l + 1, i))
                    if (l, i) in at:
                        self.assertNotEqual(out, nl.net(*g(l, i)))
                        self.assertEqual(nl.reads(out), nets(nl, [g(l, i), p(l, i), g(l, at[(l, i)])]))
                    else:
                        self.assertEqual(out, nl.net(*g(l, i)))                # a pass: the same net
        for k in range(n):
            self.assertEqual(nl.reads(nl.net("s", k)), nets(nl, [("x", k), g(levels, k)]))
        self.assertEqual(nl.net("cout"), nl.net(*g(levels, n)))

    def test_kogge_stone(self):
        self.check_prefix(adders.KOGGE_STONE, adders.kogge_stone, 8)

    def test_sklansky(self):
        self.check_prefix(adders.SKLANSKY, adders.sklansky, 8)

    def test_the_ripple_designs(self):
        n = 8
        for sha in figs.get("add-ripple").designs:
            with self.subTest(design=os.path.basename(design_path(sha))[:12]):
                nl = self.elab(sha, "add_n", N=n)
                levels, nodes = adders.ripple(n)
                carries = [nl.net("c", i) for i in range(n + 1)]
                stop = set(carries) | {b for b in nl.names["a"] + nl.names["b"] + nl.names["cin"]}
                self.assertEqual(carries[0], nl.net("cin"))
                for l, i, j in nodes:              # node l: the carry into bit i = l + 1 from carry j = l and bit l
                    self.assertEqual(nl.reads(carries[i], stop),
                                     {carries[j], nl.net("a", l), nl.net("b", l)})
                self.assertEqual(nl.net("cout"), carries[n])

    def test_carry_select(self):
        n = 16
        nl = self.elab(adders.CARRY_SELECT, "add_n", N=n)
        blocks, tail = adders.carry_select(n)
        for j, lo, hi in blocks:
            for t in range(6):
                for row in ("c0", "c1"):
                    self.assertEqual(nl.reads(nl.net(row, j * 7 + t + 1)),
                                     nets(nl, [("g", lo + t), ("p", lo + t), (row, j * 7 + t)]))
                self.assertEqual(nl.reads(nl.net("cs", j * 6 + t)),
                                 nets(nl, [("cb", j), ("c1", j * 7 + t), ("c0", j * 7 + t)]))
                self.assertEqual(nl.reads(nl.net("s", lo + t)), nets(nl, [("p", lo + t), ("cs", j * 6 + t)]))
            self.assertEqual(nl.reads(nl.net("cb", j + 1)), nets(nl, [("cb", j), ("c1", j * 7 + 6),
                                                                       ("c0", j * 7 + 6)]))
        self.assertEqual(nl.net("cb", 0), nl.net("cin"))
        lo, hi = tail
        self.assertEqual(nl.net("c", lo), nl.net("cb", len(blocks)))
        for k in range(lo, hi + 1):
            self.assertEqual(nl.reads(nl.net("c", k + 1)), nets(nl, [("g", k), ("p", k), ("c", k)]))
        self.assertEqual(nl.net("cout"), nl.net("c", n))

    def test_the_heap(self):
        n = 16
        nl = self.elab(multipliers.HEAP_42, "mul_n", N=n)
        h, leaves, inner = multipliers.heap(n)
        w = 2 * n
        S = lambda k, c: ("S", k * w + c)           # noqa: E731
        C = lambda k, c: ("C", k * w + c)           # noqa: E731
        X = lambda k, c: ("X", k * w + c)           # noqa: E731
        Y = lambda k, c: ("Y", k * w + c)           # noqa: E731
        for k, (a, b) in inner.items():
            for c in range(w):
                self.assertEqual(nl.reads(nl.net(*X(k, c))), nets(nl, [S(b, c), C(a, c), S(a, c)]))
                self.assertEqual(nl.reads(nl.net(*S(k, c))), nets(nl, [X(k, c), C(b, c), Y(k, c)]))
                if c + 1 < w:
                    self.assertEqual(nl.reads(nl.net(*Y(k, c + 1))), nets(nl, [S(b, c), C(a, c), S(a, c)]))
                    self.assertEqual(nl.reads(nl.net(*C(k, c + 1))), nets(nl, [Y(k, c), C(b, c), X(k, c)]))
        for k, (r0, r1) in leaves.items():          # leaf k holds partial-product rows r0 (S) and r1 (C): a << r & b[r]
            for c in range(w):
                for arr, r in ((S, r0), (C, r1)):
                    want = ([("b", r)] if r < n else []) + ([("a", c - r)] if 0 <= c - r < n else [])
                    self.assertEqual(nl.reads(nl.net(*arr(k, c))), nets(nl, want), (k, c, r))
        for c in range(w):
            self.assertEqual(nl.reads(nl.net("p", c)), nets(nl, [S(0, c), C(0, c), ("R", c)]))

    def test_the_dadda_stages(self):
        n = 8
        nl = self.elab(multipliers.DADDA, "mul_n", N=n)
        h0, stages = multipliers.dadda(n)
        cols, np_ = 2 * n, max(n, 2)
        at = lambda name, s, k, i: nl.net(name, (s * cols + k) * np_ + i)      # noqa: E731  ([S:0][2N-1:0][NP-1:0])
        for k in range(cols):                       # the partial products: column k's height
            self.assertEqual([isinstance(at("T", 0, k, i), int) for i in range(np_)],
                             [i < h0[k] for i in range(np_)], k)
        for s, st in enumerate(stages):
            for k in range(cols):
                f, h = st["adders"][k]
                for q in range(np_):                # adder q of column k: a full adder on bits 3q..3q+2, a half on two
                    want = 3 if q < f else 2 if q < f + h else 0
                    got = at("SM", s, k, q)
                    if want:
                        self.assertEqual(nl.reads(got), {at("T", s, k, 3 * q + b) for b in range(want)}, (s, k, q))
                    else:
                        self.assertFalse(isinstance(got, int), (s, k, q))      # no adder: a constant
                self.assertEqual([isinstance(at("T", s + 1, k, i), int) for i in range(np_)],
                                 [i < st["after"][k] for i in range(np_)], (s, k))

    def test_the_mul_array(self):
        for n in (8, 16):                           # drawn at 8; the caption's chain length is the one at 16
            with self.subTest(N=n):
                self.check_array(n)

    def check_array(self, n):
        nl = self.elab(multipliers.ARRAY_BYHAND, "mul_n", N=n)
        cell_of = {}
        for i in range(n):
            for j in range(n):
                if i:
                    cell_of[nl.net("s", i * (n + 1) + j)] = (i, j)
                    cell_of[nl.net("c", i * (n + 1) + j + 1)] = (i, j)
                else:
                    cell_of[nl.net("s", j)] = (0, j)                # row 0: pp[0] (no adder)
        stop = set(cell_of)
        for (i, j), src in multipliers.array(n).items():
            got = set()
            for out in (nl.net("s", i * (n + 1) + j), nl.net("c", i * (n + 1) + j + 1)):
                got |= {cell_of[x] for x in nl.reads(out, stop) if x in cell_of and cell_of[x] != (i, j)}
            want = set(src) | ({(0, j + 1)} if i == 1 and j + 1 < n else set())
            self.assertEqual(got, want, (i, j))

    def test_the_clmul_array(self):
        n = 8
        nl = self.elab(clmul.ARRAY, "clmul_n", N=n)
        r = lambda i, j: ("r", i * n + j)           # noqa: E731
        for (i, j), src in clmul.array(n).items():
            want = [("a", i), ("b", j)] + ([r(*src)] if src else [])
            self.assertEqual(nl.reads(nl.net(*r(i, j))), nets(nl, want), (i, j))
        chain = clmul.column_chain(n, n - 1)
        self.assertEqual(nl.net("p", n - 1), nl.net(*r(*chain[-1])))

    def test_the_clmul_column_trees(self):
        for n in (8, 6):
            nl = self.elab(clmul.TREE, "clmul_n", N=n)
            m = 2 * n - 1
            for k in range(m):
                for pos, (x, y) in clmul.tree(n).items():
                    self.assertEqual(nl.reads(nl.net("T", k * m + pos)), nets(nl, [("T", k * m + x), ("T", k * m + y)]),
                                     (n, k, pos))
                self.assertEqual(nl.net("p", k), nl.net("T", k * m + 2 * n - 2))

    def test_karatsuba_one_level(self):
        n = 16
        nl = self.elab(clmul.K1, "clmul_n", N=n)
        h, terms = clmul.karatsuba1(n)
        name = {"L": "rl", "M": "rm", "H": "rh"}

        def coeff(arr, c):                          # coefficient c of an array's product: its row c, else row H-1
            return (name[arr], c * h) if c < h else (name[arr], (h - 1) * h + c - h + 1)
        for i, ts in terms.items():
            want = nets(nl, [coeff(a, c) for a, c in ts])
            got = nl.net("pf", i)
            if not (len(want) == 1 and got in want):            # one term: pf[i] is an assign of it
                self.assertEqual(nl.reads(got), want, i)
            self.assertEqual(nl.net("p", i), nl.net("pf", i))
        for arr, lo_a, lo_b in (("rl", (0,), (0,)), ("rh", (h,), (h,)), ("rm", (0, h), (0, h))):
            for i in range(h):
                for j in range(h):
                    want = [("ap", i + o) for o in lo_a] + [("bp", j + o) for o in lo_b]
                    want += [(arr, (i - 1) * h + j + 1)] if i and j < h - 1 else []
                    self.assertEqual(nl.reads(nl.net(arr, i * h + j)), nets(nl, want), (arr, i, j))

    def test_karatsuba_levels(self):
        n = 16
        nl = self.elab(clmul.KLV, "clmul_n", N=n)
        levels, p, nodes = clmul.karatsuba_tree(n)
        t_all = 3 ** levels
        row = 4 * t_all
        for (l, t), (width, kind) in nodes.items():
            if l == 0:
                continue
            par = t // 3
            base = par * (p >> (l - 1))
            for v in ("av", "bv"):
                for b in range(width):
                    me = nl.net(v, l * row + t * width + b)
                    lo, hi = nl.net(v, (l - 1) * row + base + b), nl.net(v, (l - 1) * row + base + width + b)
                    if kind == "low":
                        self.assertEqual(me, lo)
                    elif kind == "high":
                        self.assertEqual(me, hi)
                    else:
                        self.assertEqual(nl.reads(me), {lo, hi})
        for t in range(t_all):                      # each leaf a 4 x 4 schoolbook product
            for c in range(7):
                want = [("av", levels * row + 4 * t + i) for i in range(4) if 0 <= c - i < 4]
                want += [("bv", levels * row + 4 * t + c - i) for i in range(4) if 0 <= c - i < 4]
                self.assertEqual(nl.reads(nl.net("rv", levels * 8 * t_all + 8 * t + c)), nets(nl, want))
        for l in range(levels):                     # each node's product reads its three children's, nothing else
            for t in range(3 ** l):
                slot = 2 * (p >> l)
                kids = {nl.net("rv", (l + 1) * 8 * t_all + (3 * t + c) * (p >> l) + b) for c in range(3)
                        for b in range(p >> l)}
                seen = set()
                for b in range(slot - 1):
                    me = nl.net("rv", l * 8 * t_all + t * slot + b)
                    got = {me} if me in kids else nl.reads(me)      # an assign of a child's bit, or XORs of them
                    self.assertTrue(got and got <= kids, (l, t, b))
                    seen |= got
                for c in range(3):                  # each child's product is read
                    child = {nl.net("rv", (l + 1) * 8 * t_all + (3 * t + c) * (p >> l) + b) for b in range(p >> l)}
                    self.assertTrue(seen & child, (l, t, c))

    def test_the_divider_cores(self):
        par = self.elab(divider.RESTORING, "fdiv", W=5, P=11)
        srt = self.elab(divider.SRT, "fdiv", W=5, P=11)
        steps, sw = divider.cores(11)["restoring"]
        stages, ew, fw = divider.cores(11)["srt"]

        def arith(nl):
            """{(cell type, output width, the named signal it drives)} of the add/sub cells."""
            out = []
            for c in nl.cells:
                if c["type"] in ("$add", "$sub"):
                    y = c["connections"]["Y"]
                    who = sorted({n for n, bits in nl.names.items() if not n.startswith("$") and y[0] in bits})
                    out.append((c["type"], len(y), tuple(who)))
            return out
        a_par, a_srt = arith(par), arith(srt)
        dd = [x for x in a_par if "dd" in x[2]]
        self.assertEqual(len(dd), steps)
        self.assertTrue(all(t == "$sub" and w == sw for t, w, _ in dd))
        es = [x for x in a_srt if "es" in x[2]]
        rs = [x for x in a_srt if "rs" in x[2]]
        self.assertEqual(len(es), stages)
        self.assertTrue(all(t == "$add" and w == ew for t, w, _ in es))
        self.assertEqual([(t, w) for t, w, _ in rs], [("$add", fw)])
        shared_par = sorted((t, w) for t, w, who in a_par if "dd" not in who)
        shared_srt = sorted((t, w) for t, w, who in a_srt if "es" not in who and "rs" not in who)
        self.assertEqual(shared_par, shared_srt)           # the rest of the datapath: the same adders in both
        ge_par = [c for c in par.cells if c["type"] == "$ge"]
        ge_srt = [c for c in srt.cells if c["type"] == "$ge"]
        self.assertEqual(len(ge_par), steps)
        self.assertTrue(all(len(c["connections"]["A"]) == sw for c in ge_par))
        self.assertEqual(len(ge_srt), 4 * stages)
        self.assertTrue(all(len(c["connections"]["A"]) == 7 for c in ge_srt))

    def test_the_srt_selection(self):
        n_stages = divider.cores(11)["srt"][0]
        script = ["read_verilog -sv " + design_path(divider.SRT), "hierarchy -top fdiv", "proc", "opt_clean"]
        for da in range(8):
            script.append(f"eval -set da {da} -show t2 -show t1 -show t0 -show tm")
        for da in range(8):
            for yb in range(128):
                rep = format(yb, "07b") * n_stages
                script.append(f"eval -set da {da} -set yb {7 * n_stages}'b{rep} -show g2 -show g1 -show g0 -show gm")
        path = os.path.join(self.tmp.name, "s.ys")
        with open(path, "w") as fh:
            fh.write("\n".join(script) + "\n")
        out = subprocess.run(yosys_cmd() + ["-s", path], check=True, capture_output=True, text=True).stdout
        vals = re.findall(r"Eval result: \\(\w+) = \d+'([01]+)\.", out)
        th, k = {}, 0
        for da in range(8):
            for q in (2, 1, 0, -1):
                name, bits = vals[k]
                k += 1
                th[(q, da)] = int(bits, 2)
        for (q, da), v in th.items():
            self.assertEqual(v, divider.THRESHOLDS[q][da], (q, da))
        for da in range(8):
            for yb in range(128):
                g = {}
                for name in ("g2", "g1", "g0", "gm"):
                    nm, bits = vals[k]
                    k += 1
                    self.assertEqual(nm, name)
                    self.assertIn(bits, ("0" * n_stages, "1" * n_stages))
                    g[name] = bits[0] == "1"
                got = 2 if g["g2"] else 1 if g["g1"] else 0 if g["g0"] else -1 if g["gm"] else -2
                self.assertEqual(got, divider.digit(yb, da), (da, yb))


# ---------------------------------------------------------------------------------------------------------------
# the checks against the designs: Icarus Verilog

def simulate(sv, tb, tmp):
    """Compile `sv` with the testbench text `tb` and run it: its standard output."""
    out = os.path.join(tmp, "sim")
    tbp = os.path.join(tmp, "tb.sv")
    with open(tbp, "w") as fh:
        fh.write(tb)
    subprocess.run(["iverilog", "-g2012", "-o", out, sv, tbp], check=True, capture_output=True)
    return subprocess.run(["vvp", "-n", out], check=True, capture_output=True, text=True).stdout


@unittest.skipIf(missing("iverilog", "vvp"), missing("iverilog", "vvp"))
class IcarusTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def test_the_sorter_table_is_both_designs(self):
        n, w = clocked.SORTER_N, clocked.SORTER_W
        rows = clocked.sorter_run(n, clocked.SORTER_INPUTS, clocked.SORTER_EDGES)
        ins = list(clocked.SORTER_INPUTS)
        stim = "".join(f"    in_valid = {1 if e < len(ins) else 0}; in_data = {ins[e] if e < len(ins) else 0};\n"
                       "    @(posedge clk); #1;\n"
                       '    $display("%0d %0d %0d %0d", dut.data, dut.tok, out_valid, out_data);\n'
                       "    @(negedge clk);\n" for e in range(clocked.SORTER_EDGES))
        tb = (f"module tb; logic clk = 0, rst = 1, start = 0, in_valid = 0; logic [{w - 1}:0] in_data = 0;\n"
              f"  logic out_valid; logic [{w - 1}:0] out_data;\n"
              f"  sorter #(.N({n}), .W({w})) dut(.*);\n  always #5 clk = ~clk;\n"
              "  initial begin\n    @(negedge clk); @(negedge clk); rst = 0;\n"
              '    $display("%0d %0d", dut.data, dut.tok);\n' + stim + "    $finish;\n  end\nendmodule\n")
        for sha in figs.get("sorter-insertion").designs:
            with self.subTest(design=os.path.basename(design_path(sha))[:12]):
                lines = simulate(design_path(sha), tb, self.tmp.name).split("\n")
                self.assertEqual(lines[0], "0 0")                          # after reset: every cell and token 0
                for s, line in zip(rows, lines[1:]):
                    data, tok, ov, od = map(int, line.split())
                    self.assertEqual([(data >> (k * w)) & ((1 << w) - 1) for k in range(n)], s["cells"])
                    self.assertEqual([(tok >> k) & 1 for k in range(n)], s["tok"])
                    self.assertEqual((ov, od), (s["ov"], s["od"]))

    def test_the_arbiter_table(self):
        n = clocked.ARB_N
        rows = clocked.arbiter_run(n, clocked.ARB_REQS)
        stim = "".join(f"    req = {r};\n    @(posedge clk); #1;\n"
                       '    $display("%0d %0d", gnt, dut.mask);\n    @(negedge clk);\n' for r in clocked.ARB_REQS)
        tb = (f"module tb; logic clk = 0, rst = 1; logic [{n - 1}:0] req = 0, gnt;\n"
              f"  arbiter #(.N({n})) dut(.*);\n  always #5 clk = ~clk;\n"
              '  initial begin\n    @(negedge clk); @(negedge clk); rst = 0;\n    $display("%0d %0d", gnt, dut.mask);\n'
              + stim + "    $finish;\n  end\nendmodule\n")
        lines = simulate(design_path(clocked.RR_MASK), tb, self.tmp.name).split("\n")
        self.assertEqual(lines[0], f"0 {(1 << n) - 1}")
        for s, line in zip(rows, lines[1:]):
            gnt, mask = map(int, line.split())
            self.assertEqual((gnt, mask), (s["gnt"], s["mask_after"]))

    def matmul_tb(self, n, w, acc, a, b, edges, extra=""):
        def pack(m, width):
            v = 0
            for i in range(n):
                for j in range(n):
                    v |= (m[i][j] & ((1 << width) - 1)) << ((i * n + j) * width)
            return v
        return (f"module tb; logic clk = 0, rst = 1, start = 0; logic [{n * n * w - 1}:0] A = {n * n * w}'d"
                f"{pack(a, w)}, B = {n * n * w}'d{pack(b, w)};\n  logic done; logic [{n * n * acc - 1}:0] C;\n"
                f"  matmul #(.N({n}), .W({w}), .AccW({acc})) dut(.*);\n  always #5 clk = ~clk;\n"
                "  initial begin\n    @(negedge clk); @(negedge clk); rst = 0; start = 1;\n"
                "    @(posedge clk); #1; @(negedge clk); start = 0;\n"
                f"    repeat ({edges}) begin @(posedge clk); #1; $display(\"%0d %0d{' %0d' if extra else ''}\", "
                f"done, C{', ' + extra if extra else ''}); @(negedge clk); end\n    $finish;\n  end\nendmodule\n")

    def test_the_matmul_schedules(self):
        n, w, acc = 4, 8, 32
        rnd = random.Random(3)
        a = [[rnd.randrange(-128, 128) for _ in range(n)] for _ in range(n)]
        b = [[rnd.randrange(-128, 128) for _ in range(n)] for _ in range(n)]
        mask = (1 << acc) - 1

        def entries(v):
            return [[(v >> ((i * n + j) * acc)) & mask for j in range(n)] for i in range(n)]

        def partial(ks):
            return [[sum(a[i][k] * b[k][j] for k in ks) & mask for j in range(n)] for i in range(n)]
        for name, v, sha in (("matmul-schedule-g1", "g1", matmul.G1), ("matmul-schedule-four", "four", matmul.FOUR),
                             ("matmul-schedule-two", "two", matmul.TWO), ("matmul-schedule-free", "free", matmul.FREE),
                             ("matmul-schedule-reg", "reg", matmul.REG)):
            with self.subTest(figure=name):
                self.assertEqual(figs.get(name).designs, (sha,))
                rows = matmul.schedule(v)
                lines = simulate(design_path(sha), self.matmul_tb(n, w, acc, a, b, len(rows) + 2,
                                                                  "dut.P" if v == "reg" else ""), self.tmp.name)
                lines = lines.split("\n")
                for s, line in zip(rows, lines):
                    vals = list(map(int, line.split()))
                    self.assertEqual(bool(vals[0]), s["done"], s["edge"])
                    self.assertEqual(entries(vals[1]), partial(s["C"]), s["edge"])
                    if v == "reg":
                        self.assertEqual(entries(vals[2]), partial(s["P"]), s["edge"])
                # after the figure's last edge nothing changes (the product stays in C, done stays up)
                for line in lines[len(rows):len(rows) + 2]:
                    vals = list(map(int, line.split()))
                    self.assertEqual((vals[0], entries(vals[1])), (1, partial(range(n))))

    def test_the_spatial_pipeline(self):
        n, w, acc = 4, 8, 32
        rnd = random.Random(4)
        a = [[rnd.randrange(-128, 128) for _ in range(n)] for _ in range(n)]
        b = [[rnd.randrange(-128, 128) for _ in range(n)] for _ in range(n)]
        mask = (1 << acc) - 1
        levels, names, table, into_c, done = matmul.pipeline(n)
        dot = lambda m: sum(a[m // n][k] * b[k][m % n] for k in range(n)) & mask        # noqa: E731
        # after each edge: done, C's top word (C is never cleared), and every stage the figure draws: the operand
        # registers' lane 0, the leaf of lane 0 (its product), tree node 1 (lanes 0 and 1) and the root (node 0)
        p_leaves = 1 << levels
        probes = (f"dut.pcu_va[{acc - 1}:0], dut.pcu_vb[{acc - 1}:0], dut.pcu_tr[{p_leaves * acc - 1}:"
                  f"{(p_leaves - 1) * acc}], dut.pcu_tr[{2 * acc - 1}:{acc}], dut.pcu_tr[{acc - 1}:0]")
        tb = self.matmul_tb(n, w, acc, a, b, done, probes).replace(
            ", done, C,", f", done, C[{n * n * acc - 1}:{(n * n - 1) * acc}],").replace(
            '"%0d %0d %0d"', '"%0d %0d %0d %0d %0d %0d %0d"')
        tb = tb.replace("    $finish;", '    $display("%0d", C);\n    $finish;')
        lines = simulate(design_path(matmul.PIPE), tb, self.tmp.name).split("\n")
        sx = lambda v: (v & mask) - ((v & mask) >> (acc - 1) << acc)            # noqa: E731  (AccW bits, signed)
        self.assertEqual(levels, 2)                 # the stages below: operands, products, tree level 1, root
        for t in range(1, done + 1):                # line t - 1 is after edge t
            dn, top, va, vb, leaf, node1, root = lines[t - 1].split()
            self.assertEqual(dn == "1", t >= done, t)
            row = table[t]
            if row[1] is not None:                  # operands: lane 0 holds A[i][0] and B[0][j] of its item
                i, j = divmod(row[1], n)
                self.assertEqual((sx(int(va)), sx(int(vb))), (a[i][0], b[0][j]), t)
            if row[2] is not None:                  # products: lane 0's leaf
                i, j = divmod(row[2], n)
                self.assertEqual(int(leaf), (a[i][0] * b[0][j]) & mask, t)
            if row[3] is not None:                  # tree level 1: node 1 = lanes 0 and 1
                i, j = divmod(row[3], n)
                self.assertEqual(int(node1), (a[i][0] * b[0][j] + a[i][1] * b[1][j]) & mask, t)
            m = row[levels + 2]                     # the root stage's item after edge t
            if m is not None:
                self.assertEqual(int(root), dot(m), t)
            if t in into_c:
                self.assertEqual(int(top), dot(into_c[t]), t)
        c = int(lines[done])
        self.assertEqual([(c >> (k * acc)) & mask for k in range(n * n)], [dot(m) for m in range(n * n)])


if __name__ == "__main__":
    unittest.main()
