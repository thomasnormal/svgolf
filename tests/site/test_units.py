"""Unit tests of the site generator's parts: the highlighter, the Markdown
renderer, the chart scales and drawings, the combined score, the Lean
declaration index and the property panel's checks.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)
"""

import glob
import html
import importlib.util
import json
import os
import re
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
sys.path.insert(0, SITE)

import highlight   # noqa: E402
import leansrc     # noqa: E402
import md          # noqa: E402
import props       # noqa: E402
import svgplot     # noqa: E402


def _ls_root():
    spec = importlib.util.spec_from_file_location("svgolf_layout_units", os.path.join(SVGOLF, "check", "layout.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.LS_ROOT


LS_ROOT = _ls_root()


def repo_file(rel):
    """A repository path (`svgolf/...` or lean-surfaces' own, as site/build.py writes them)."""
    if rel.startswith("svgolf/"):
        return os.path.join(SVGOLF, *rel.split("/")[1:])
    return os.path.join(LS_ROOT, rel)


def repo_text(rel):
    with open(repo_file(rel), encoding="utf-8") as fh:
        return fh.read()


def source_files(*exts):
    """Every file of svGolf with one of the extensions, build trees excluded."""
    out = []
    for ext in exts:
        out += glob.glob(os.path.join(SVGOLF, "**", "*" + ext), recursive=True)
    return sorted(p for p in out if "/.lake/" not in p and "/_out/" not in p)


def strip_tags(s):
    return html.unescape(re.sub(r"<[^>]+>", "", s))


class HighlightTest(unittest.TestCase):
    def check_round_trip(self, paths, lang):
        self.assertTrue(paths)
        for p in paths:
            with open(p, encoding="utf-8") as fh:
                text = fh.read()
            with self.subTest(file=os.path.relpath(p, SVGOLF)):
                toks = highlight.tokens(text, lang)
                self.assertEqual("".join(t for _, t in toks), text)
                self.assertEqual(strip_tags(highlight.highlight(text, lang)), text)

    def test_every_lean_file_round_trips(self):
        self.check_round_trip(source_files(".lean"), "lean")

    def test_every_sv_file_round_trips(self):
        self.check_round_trip(source_files(".sv"), "sv")

    def test_bash_and_unknown_languages_round_trip(self):
        text = 'cd svgolf\nX=1 python3 check.py --unproved "a b" \\\n  --keep  # done\n'
        self.assertEqual("".join(t for _, t in highlight.tokens(text, "bash")), text)
        self.assertEqual(highlight.tokens("anything <at> all", None), [(None, "anything <at> all")])

    def test_token_kinds(self):
        def kinds(text, lang):
            return [(k, t) for k, t in highlight.tokens(text, lang) if k]
        self.assertEqual(kinds("theorem t : 1 = 1 := by /- a /- b -/ -/ rfl -- c", "lean"),
                         [("kw", "theorem"), ("num", "1"), ("num", "1"), ("kw", "by"),
                          ("com", "/- a /- b -/ -/"), ("com", "-- c")])
        self.assertEqual(kinds("assign y = 4'b1z0 | $clog2(N); // c", "sv"),
                         [("kw", "assign"), ("num", "4'b1z0"), ("sys", "$clog2"), ("com", "// c")])
        self.assertEqual(kinds("LEAN_PATH=x lake build --quiet # c", "bash"),
                         [("var", "LEAN_PATH"), ("cmd", "lake"), ("opt", "--quiet"), ("com", "# c")])
        self.assertIn('<span class="hl-kw">module</span>', highlight.highlight("module m; endmodule", "sv"))
        self.assertEqual(highlight.highlight("a < b & c", "sv"), "a &lt; b &amp; c")


def render(text, **kw):
    return md.render(text, source="t.md", **kw).html


class MarkdownTest(unittest.TestCase):
    def test_angle_brackets_are_always_text(self):
        out = render("Run `check.py tasks/<name>` on <name>.sv, <b>not bold</b>.")
        self.assertIn("<code>check.py tasks/&lt;name&gt;</code>", out)
        self.assertIn("on &lt;name&gt;.sv, &lt;b&gt;not bold&lt;/b&gt;.", out)
        self.assertNotIn("<b>", out)

    def test_headings_get_unique_anchors(self):
        r = md.render("# Top\n\n## The `banlist`\n\n## The banlist\n\n### Rules (v0)", source="t.md")
        self.assertEqual([h[2] for h in r.headings], ["top", "the-banlist", "the-banlist-1", "rules-v0"])
        self.assertIn('<h2 id="the-banlist">The <code>banlist</code>', r.html)
        shifted = md.render("## Sub", source="t.md", heading_shift=1)
        self.assertTrue(shifted.html.startswith('<h3 id="sub">'))

    def test_code_spans(self):
        self.assertIn("<code>a`b</code>", render("x `` a`b `` y"))
        self.assertIn("<code>**not bold**</code>", render("`**not bold**`"))
        self.assertIn("an unmatched ` tick", render("an unmatched ` tick"))

    def test_emphasis_is_strict_about_operators(self):
        self.assertIn("<strong>bold</strong> and <em>em</em> and <em>u</em>", render("**bold** and *em* and _u_"))
        for text in ("LeanModels.Sv.*, SvGolf.*, tasks.*", "a * b * c", "bans + - * / % ** at run time",
                     "keep area_mge and row_key"):
            with self.subTest(text=text):
                out = render(text)
                self.assertNotIn("<em>", out)
                self.assertNotIn("<strong>", out)

    def test_backslash_escapes(self):
        self.assertIn("*not em*", render(r"\*not em\*"))
        self.assertIn("a|b", render(r"a\|b"))

    def test_links_go_through_the_resolver(self):
        seen = []

        def resolve(target):
            seen.append(target)
            return None if target.startswith("score/") else "page.html#x"
        out = render("[the rules](README.md#rules), [PPA](score/PPA.md), [`code` link](https://zk.golf)",
                     resolve_link=resolve)
        self.assertEqual(seen, ["README.md#rules", "score/PPA.md", "https://zk.golf"])
        self.assertIn('<a href="page.html#x">the rules</a>', out)
        self.assertIn('<span class="unlinked" title="score/PPA.md">PPA</span>', out)
        self.assertIn('<a href="page.html#x"><code>code</code> link</a>', out)
        self.assertIn("a [bracket] alone", render("a [bracket] alone"))

    def test_tables(self):
        out = render("| a | b | c |\n|:--|--:|:-:|\n| `x|y` | 1 \\| 2 | |\n| only one |")
        self.assertIn('<th class="al-left">a</th><th class="al-right">b</th><th class="al-center">c</th>', out)
        self.assertIn('<td class="al-left"><code>x|y</code></td><td class="al-right">1 | 2</td>', out)
        self.assertIn('<td class="al-left">only one</td><td class="al-right"></td><td class="al-center"></td>', out)
        self.assertIn('<div class="table-wrap"><table>', out)

    def test_nested_tight_and_loose_lists(self):
        out = render("1. first\n   continued\n   * inner\n     more\n2. second\n\nafter")
        self.assertEqual(out, "<ol>\n<li>first\ncontinued\n<ul>\n<li>inner\nmore</li>\n</ul></li>\n"
                              "<li>second</li>\n</ol>\n<p>after</p>")
        loose = render("* one\n\n* two\n")
        self.assertIn("<li><p>one</p></li>", loose)
        self.assertIn('<ol start="3">', render("3. three\n4. four"))

    def test_a_list_interrupts_a_paragraph_and_lazy_lines_continue_an_item(self):
        out = render("Every source is refused, exactly:\n* the gate\nlazy line\n* the stage")
        self.assertIn("<p>Every source is refused, exactly:</p>\n<ul>\n<li>the gate\nlazy line</li>", out)
        self.assertIn("year\n2026. was", render("year\n2026. was"))   # only `1.` interrupts a paragraph

    def test_code_blocks(self):
        out = md.render("* item\n\n  ```lean\n  theorem x : True := trivial\n  ```\n", source="t.md",
                        highlight=lambda code, lang: f"[{lang}]{code}").html
        self.assertIn('<pre class="code" data-lang="lean"><code>[lean]theorem x : True := trivial</code></pre>', out)
        self.assertIn("<pre class=\"code\"><code>    p[k] = a &amp; b</code></pre>",
                      render("text\n\n        p[k] = a & b\n\nmore"))
        self.assertIn("# not a heading", render("```\n# not a heading\n```"))

    def test_unsupported_constructs_fail_with_file_and_line(self):
        cases = {
            "> a quote": "blockquote",
            "text\n\n![img](x.png)": "image",
            "[ref]: https://example.com": "reference-style",
            "Title\n=====": "setext",
            "see [^1]": "footnote",
            "\tindented": "tab",
            "| a |\n|---|\n| 1 | 2 |": "cells",
            "```\nnever closed": "unterminated",
            '[x](url "title")': "link",
        }
        for text, why in cases.items():
            with self.subTest(text=text):
                with self.assertRaises(md.MarkdownError) as e:
                    md.render("ok\n\n" + text, source="doc.md", first_line=10)
                self.assertRegex(str(e.exception), r"^doc\.md:1[2-4]: ")
                self.assertIn(why, str(e.exception).lower())

    def test_split_sections_skips_fenced_code(self):
        text = "# T\n\n## A\n\n```bash\n# comment\n```\n\n### A.1\n\n## B\nend"
        self.assertEqual(md.split_sections(text), [(1, "T", 0, 12), (2, "A", 2, 10), (3, "A.1", 8, 10),
                                                   (2, "B", 10, 12)])

    def test_every_source_document_renders(self):
        docs = [os.path.join(SVGOLF, "README.md"), os.path.join(SVGOLF, "PROVING.md")]
        docs += glob.glob(os.path.join(SVGOLF, "tasks", "*", "README.md"))
        docs += glob.glob(os.path.join(SITE, "content", "*.md"))
        docs += glob.glob(os.path.join(SITE, "content", "tasks", "*.md"))
        for p in sorted(docs):
            with self.subTest(doc=os.path.relpath(p, SVGOLF)), open(p, encoding="utf-8") as fh:
                r = md.render(fh.read(), source=p, resolve_link=lambda t: t)
                self.assertTrue(r.html)
        with open(os.path.join(SITE, "content", "roadmap.json"), encoding="utf-8") as fh:
            roadmap = json.load(fh)
        for item in roadmap["items"]:
            md.render_inline(item["title"])
            md.render_inline(item["text"])


class ChartTest(unittest.TestCase):
    def test_scales_switch_to_log_past_ten_times(self):
        self.assertFalse(svgplot.Scale(100, 999, 0, 1).log)
        self.assertTrue(svgplot.Scale(100, 1001, 0, 1).log)
        self.assertFalse(svgplot.Scale(0, 50, 0, 1).log)          # zero cannot go on a log axis
        s = svgplot.Scale(5, 5, 0, 100, integer=True)              # a single value still gets a range
        self.assertLess(s.lo, 5)
        self.assertGreater(s.hi, 5)
        self.assertTrue(all(s.lo <= t <= s.hi for t in s.ticks()))

    def test_step_line_and_rounding(self):
        self.assertEqual(svgplot.step_points([(30, 100), (10, 300), (20, 200)]),
                         [(10, 300), (20, 300), (20, 200), (30, 200), (30, 100)])
        pts = [{"id": "r", "kind": "record", "x": 33, "y": 112.0, "tip": ["r", "a submission"],
                "attrs": {"hash": "a" * 64, "frontier": "true"}, "href": "records/a.html"},
               {"id": "p", "kind": "reference", "x": 28, "y": 127.658, "tip": ["p"]},
               {"id": "q", "kind": "reference", "x": 40, "y": 130.0, "tip": ["q"]},
               {"id": "b", "kind": "baseline", "x": 17, "y": 1955.975, "tip": ["b"], "banned": True}]
        front = ["p", "r"]                                         # q is beaten by both; b is not proved
        for compact in (False, True):
            svg = svgplot.scatter_chart(pts, x_label="depth", y_label="area (GE)", front=front, title="t",
                                        compact=compact)
            numbers = re.findall(r'(?:x|y|x1|x2|y1|y2|cx|cy)="(-?[\d.]+)"', svg)
            self.assertTrue(numbers)
            self.assertTrue(all(re.fullmatch(r"-?\d+\.\d", n) for n in numbers), numbers[:5])
            self.assertIn("log scale", svg)                        # 112 to 1956 spans more than 10x
            self.assertEqual(svg.count('<g class="mark'), 4)
            self.assertEqual(svg.count("on-front"), 2)
            self.assertIn('<a href="records/a.html" aria-label="r">', svg)
            self.assertIn('data-tip="r&#10;a submission"', svg.replace("\n", "&#10;"))
        self.assertEqual(svgplot.scatter_chart([], x_label="x", y_label="y", title="t"), "")

    def test_score_chart(self):
        entries = [{"id": "a", "kind": "reference", "date": "2026-10-29", "value": 90.5, "score": 905, "tip": ["a"]},
                   {"id": "b", "kind": "reference", "date": "2026-10-30", "value": 52.3, "score": 523, "tip": ["b"]},
                   {"id": "c", "kind": "record", "date": "2026-11-02", "value": 60.0, "score": 600, "tip": ["c"]}]
        levels = [{"id": "x", "name": "dadda", "value": 45.9, "banned": False, "tip": ["x"]},
                  {"id": "y", "name": "yosys", "value": 56.5, "banned": True, "tip": ["y"]}]
        svg = svgplot.score_chart(entries, par={"value": 52.3, "label": "par"}, levels=levels, title="t",
                                  unit="u", until="2026-11-04")
        self.assertEqual(svg.count('class="mark best"'), 2)        # a and b set a new best, c does not
        self.assertEqual(svg.count('<line class="par-line"'), 1)
        self.assertEqual(svg.count('<line class="level"'), 2)
        for text in (">PAR<", ">dadda<", ">yosys<", "not proved", "banned op"):
            self.assertIn(text, svg)
        compact = svgplot.score_chart(entries, par={"value": 52.3, "label": "par"}, levels=levels, title="t",
                                      unit="u", compact=True)
        self.assertNotIn(">dadda<", compact)                      # named under the chart instead
        self.assertIn('viewBox="0 0 420 ', compact)
        logs = svgplot.score_chart(entries, levels=levels, title="t", unit="u", log=True)
        self.assertIn("log scale", logs)
        self.assertEqual(svgplot.score_chart([dict(entries[0], date=None)], title="t", unit="u"), "")

    def test_log_ticks_inside_one_decade(self):
        s = svgplot.Scale(1198, 1682, 0, 1, log=True)
        self.assertTrue(s.log)
        ticks = s.ticks()
        self.assertGreaterEqual(len(ticks), 3)
        self.assertTrue(all(s.lo <= t <= s.hi for t in ticks))
        wide = svgplot.Scale(310961, 1342478, 0, 1, log=True)       # a phone's drawing gets fewer
        self.assertLessEqual(len(wide.ticks(4)), 6)
        self.assertLess(len(wide.ticks(4)), len(wide.ticks(6)))

    def test_designs_at_one_point_share_one_tooltip(self):
        """Designs drawn at the same (x, y) hide one another: each one's tooltip names them all
        (the ones on the front first), with the shared values; a point alone keeps its own tip, and
        a linked mark keeps its own name."""
        pts = [{"id": "b", "kind": "reference", "x": 112, "y": 33, "tip": ["b", "k", "Score: 1"], "brief": "b · ref",
                "axis_tip": ["Area: 112", "Depth: 33"], "href": "b.html"},
               {"id": "a", "kind": "reference", "x": 112, "y": 33, "tip": ["a"], "brief": "a · ref · par",
                "axis_tip": ["Area: 112", "Depth: 33"]},
               {"id": "c", "kind": "baseline", "x": 120, "y": 28, "tip": ["c", "alone"]}]
        out = svgplot.shared_tips(pts, {"a", "b"})
        self.assertEqual([p["id"] for p in out], ["b", "a", "c"])
        group = ["2 designs at this point", "a · ref · par", "b · ref", "Area: 112", "Depth: 33"]
        self.assertEqual(out[0]["tip"], group)
        self.assertEqual(out[1]["tip"], group)
        self.assertEqual(out[2]["tip"], ["c", "alone"])
        svg = svgplot.scatter_chart(pts, x_label="x", y_label="y", front=["a", "b"], title="t")
        self.assertEqual(svg.count("2 designs at this point\n"), 2)
        self.assertIn('<a href="b.html" aria-label="b">', svg)

    def test_levels_carry_their_tooltip_and_compact_titles_run_across(self):
        entries = [{"id": "a", "kind": "reference", "date": "2026-10-29", "value": 90.5, "score": 905, "tip": ["a"]}]
        levels = [{"id": "x", "name": "dadda", "value": 45.9, "banned": False, "tip": ["dadda", "baseline"]}]
        for compact in (False, True):
            svg = svgplot.score_chart(entries, levels=levels, title="t", unit="u", compact=compact)
            self.assertIn('data-tip="dadda\nbaseline"', svg)
            self.assertEqual(svg.count('<line class="level-hit"'), 1)
            self.assertEqual(svg.count('<line class="drop"'), 1)
            self.assertEqual("rotate(-90)" in svg, not compact)    # a phone's y title: across the top
        scatter = svgplot.scatter_chart([{"id": "p", "kind": "reference", "x": 1, "y": 2, "tip": ["p"]}],
                                        x_label="x", y_label="y", title="t", compact=True)
        self.assertNotIn("rotate(-90)", scatter)

    def lines(self):
        def pts(ys):
            return [{"x": x, "y": y, "tip": [f"x={x}"]} for x, y in zip((8, 16, 32, 64), ys)]
        return [{"id": "line/a", "kind": "reference", "banned": False, "name": "ripple", "href": "#ref-a",
                 "tip": ["ripple", "proved reference"], "pts": pts((1, 1, 1, 1))},
                {"id": "line/b", "kind": "baseline", "banned": False, "name": "a_very_long_baseline_name_indeed",
                 "href": None, "tip": ["b"], "pts": pts((1.1, 1.05, 1.0, 0.95))},
                {"id": "line/c", "kind": "baseline", "banned": True, "name": "plus", "href": None, "tip": ["c"],
                 "pts": pts((1.0, 1.01, 1.02, 1.0))},
                {"id": "line/d", "kind": "baseline", "banned": False, "name": "one", "href": None, "tip": ["d"],
                 "pts": pts((2,))}]

    def test_the_scaling_view_draws_one_line_per_design(self):
        """svgplot.line_chart: a polyline per design with two points or more (a one-point design is not a line), a
        mark per point, the names in the right margin at least a line apart (the close ends of b, c and a are pushed
        apart), x ticks at exactly the parameter values, the guide level, deterministic. Its marks are not the
        explorer's (`data-line-kind`, never `data-kind`: one design is several marks here)."""
        for compact in (False, True):
            svg = svgplot.line_chart(self.lines(), x_label="N", y_label="Score ÷ par's", x_ticks=[8, 16, 32, 64],
                                     x_log=True, guide={"y": 1, "label": "par: ripple"}, title="t", compact=compact)
            self.assertEqual(svg, svgplot.line_chart(self.lines(), x_label="N", y_label="Score ÷ par's",
                                                     x_ticks=[8, 16, 32, 64], x_log=True,
                                                     guide={"y": 1, "label": "par: ripple"}, title="t", compact=compact))
            self.assertEqual(svg.count('<g class="series"'), 3)
            self.assertNotIn(">one<", svg)
            self.assertEqual(svg.count('class="series-line s-baseline"'), 2)
            self.assertEqual(svg.count('class="series-line s-reference"'), 1)
            self.assertEqual(svg.count('<g class="mark"'), 12)
            self.assertNotIn("data-kind=", svg)
            self.assertEqual(svg.count('<line class="par-line"'), 1)
            self.assertEqual(svg.count('<a href="#ref-a"'), 4)
            ticks = re.findall(r'<text class="tick" [^>]*text-anchor="middle">([^<]*)</text>', svg)
            self.assertEqual(ticks, ["8", "16", "32", "64"])
            self.assertIn("N, log scale", svg)
            names = [(float(y), n) for y, n in re.findall(r'<text class="lv-name" x="[^"]*" y="([^"]*)">([^<]*)</text>',
                                                          svg)]
            self.assertEqual(len(names), 3)
            ys = sorted(y for y, _ in names)
            self.assertTrue(all(b - a >= (16 if compact else 15) - 0.11 for a, b in zip(ys, ys[1:])), ys)
            self.assertIn("a_very_long_…" if compact else "a_very_long_baseline_name…", [n for _, n in names])
        self.assertEqual(svgplot.line_chart(self.lines()[3:], x_label="N", y_label="y", x_ticks=[16], title="t"), "")

    def test_tick_labels_say_the_tick_exactly(self):
        """svgplot.tick: num's form (k, M, 4 digits) unless that rounds the tick (fdivp's binary32 delays sit 2.5k apart:
        147.5k, never 148k); charts.js's num is the same rule."""
        self.assertEqual([svgplot.tick(v) for v in (147500, 150000, 152500, 160000)],
                         ["147.5k", "150k", "152.5k", "160k"])
        self.assertEqual([svgplot.tick(v) for v in (0, 0.8, 1.25, 1012.5, 2000, 20000, 1500000, 1250000)],
                         ["0", "0.8", "1.25", "1012.5", "2000", "20k", "1.5M", "1.25M"])
        for v in (0.8, 1.25, 2000, 20000, 1500000):               # where num is exact, tick is num
            self.assertEqual(svgplot.tick(v), svgplot.num(v))
        with open(os.path.join(SITE, "charts.js"), encoding="utf-8") as fh:
            self.assertIn("svgplot.tick", fh.read())

    def test_close_named_ticks_take_two_rows(self):
        """svgplot.tick_rows / line_chart: tick labels that would overlap (fdivp's bfloat16 at P = 8 and binary16 at
        P = 11 on a phone's drawing) drop to a second row, and the drawing grows by that row (the plot is the same);
        labels with room stay on one row."""
        self.assertEqual(svgplot.tick_rows([100, 140, 300], ["bfloat16", "binary16", "binary32"], 9.0), [0, 1, 0])
        self.assertEqual(svgplot.tick_rows([100, 300, 500], ["bfloat16", "binary16", "binary32"], 9.0), [0, 0, 0])
        lines = [{"id": f"line/{k}", "kind": "reference", "banned": False, "name": k, "href": None, "tip": [k],
                  "pts": [{"x": x, "y": y, "tip": ["p"]} for x, y in zip((8, 11, 24), ys)]}
                 for k, ys in (("a", (1, 1, 1)), ("b", (4, 3.6, 3.5)))]
        names = {8: "bfloat16", 11: "binary16", 24: "binary32"}

        def draw(compact):
            return svgplot.line_chart(lines, x_label="P", y_label="y", x_ticks=[8, 11, 24], x_fmt=names.get,
                                      x_log=False, title="t", compact=compact)
        phone, wide = draw(True), draw(False)
        self.assertIn('viewBox="0 0 420 416"', phone)
        rows = re.findall(r'<text class="tick" x="[^"]*" y="([^"]*)" text-anchor="middle">', phone)
        self.assertEqual(rows, ["366.0", "382.0", "366.0"])
        self.assertIn('<text class="axis-title" x="182.0" y="408.0"', phone)
        self.assertIn('viewBox="0 0 960 430"', wide)              # room for all three on one row
        self.assertEqual(len(set(re.findall(r'<text class="tick" x="[^"]*" y="([^"]*)" text-anchor="middle">',
                                            wide))), 1)

    def test_the_measured_data_loader_refuses_stale_data(self):
        """metrics.load_measured: the data of another sky130 identity or input drive is not used (a warning)."""
        import metrics
        warned = []
        ident = {"ppa_version": "sky130_a0_v3"}
        with open(os.path.join(SVGOLF, "score", "measured", "add.json"), encoding="utf-8") as fh:
            have = json.load(fh)["identity"]
        good = {k: have[k] for k in ("ppa_version", "ppa_pins_sha256", "liberty_sha256")}
        self.assertIsNotNone(metrics.load_measured("add", good, have["input_drive"], warn=warned.append))
        self.assertEqual(warned, [])
        self.assertIsNone(metrics.load_measured("add", dict(good, ppa_version="sky130_a0_v9"), have["input_drive"],
                                                warn=warned.append))
        self.assertIsNone(metrics.load_measured("add", good, "sky130_fd_sc_hd__buf_1", warn=warned.append))
        self.assertEqual(len(warned), 2)
        self.assertIsNone(metrics.load_measured("no_such_task", ident, None, warn=warned.append))
        self.assertEqual(len(warned), 2)                 # no data is not a warning


class PageTest(unittest.TestCase):
    """page.py's components."""

    def test_a_stacking_table_names_each_cell(self):
        import page
        t = page.table(["design", page.Html('score (<span class="nocase">µm²</span>)'), "depth"],
                       [["<code>a</code>", "1", "2"]], numeric=(1, 2), stack=True)
        self.assertIn('<table class="stack">', t)
        self.assertIn('<td class="num" data-label="score (µm²)">1</td>', t)
        self.assertIn('<td data-label="design"><code>a</code></td>', t)
        plain = page.table(["a", "b", "c", "d", "e"], [["1", "2", "3", "4", "5"]])
        self.assertIn('<table class="wide">', plain)
        self.assertNotIn("data-label", plain)


class CombinedTest(unittest.TestCase):
    """leaderboard/combined.py: the score is area x time, exact in integers."""

    def setUp(self):
        import metrics
        self.c = metrics.combined

    def test_exact_and_display(self):
        c = self.c
        self.assertEqual(c.exact(4604416, 2602), 4604416 * 2602)       # add_n: 460.4416 um^2, 2602 ps
        self.assertAlmostEqual(c.um2ns(c.exact(4604416, 2602)), 460.4416 * 2.602)
        self.assertEqual(c.time_ps(cycles=4, period_ps=10705), 42820)
        self.assertEqual(c.of_columns(area_um2=87173.6064, time=42820), 871736064 * 42820)
        self.assertIsNone(c.exact(None, 5))
        self.assertIsNone(c.time_ps(cycles=4))
        self.assertEqual(c.fmt(1198.069), "1198")
        self.assertEqual(c.fmt(52338.36), "52\u202f338")
        self.assertEqual(c.fmt(118.44), "118.4")
        self.assertEqual(c.fmt(None), "–")

    def test_of_record(self):
        c = self.c
        rec = {"score": {"area_mge": 1, "depth": 1},
               "ppa": {"available": True, "area_e4um2_sky130": 4604416, "delay_ps_sky130": 2602}}
        self.assertEqual(c.of_record(rec), 4604416 * 2602)
        self.assertIsNone(c.of_record({"score": {}, "ppa": None}))
        self.assertIsNone(c.of_record({"score": {}, "ppa": {"available": False, "reason": "no liberty"}}))
        clocked = {"score": {"area_um2": 87173.6064, "time_ps": 42820, "cycles": 4, "period_ps": 10705}}
        self.assertEqual(c.of_record(clocked), 871736064 * 42820)


LEAN_SAMPLE = """import X

/-!
# A module docstring: prose that looks like code is not a declaration
def NotADecl : Nat := 0
namespace Fake
-/

namespace A.B

/-- Doc of `f`. -/
@[simp]
def f (n : Nat) : Nat :=
  n + 1

-- a plain comment is not the declaration's
theorem f_pos : 0 < f 0 := by
  simp [f]

/-- The relation. -/
def Rel (a b : Nat) : Prop := a = b

@[inherit_doc] scoped infix:50 " ≈≈ " => Rel

namespace C
structure S where
  x : Nat
deriving Repr
end C

inductive T
| a
| b

instance : Inhabited T := ⟨.a⟩

def _root_.top : Nat := 1

end A.B

def g : String := "def h : Nat := 2"
"""


class LeanSrcTest(unittest.TestCase):
    def test_declarations_of_a_small_file(self):
        decls = {d.name: d for d in leansrc.declarations(LEAN_SAMPLE)}
        self.assertEqual(sorted(decls), ["A.B.C.S", "A.B.Rel", "A.B.T", "A.B.f", "A.B.f_pos", "g", "top"])
        ex = {n: leansrc.excerpt(LEAN_SAMPLE, d) for n, d in decls.items()}
        self.assertEqual(ex["A.B.f"], "/-- Doc of `f`. -/\n@[simp]\ndef f (n : Nat) : Nat :=\n  n + 1")
        self.assertEqual(ex["A.B.f_pos"], "theorem f_pos : 0 < f 0 := by\n  simp [f]")
        self.assertEqual(ex["A.B.Rel"], '/-- The relation. -/\ndef Rel (a b : Nat) : Prop := a = b\n\n'
                                        '@[inherit_doc] scoped infix:50 " ≈≈ " => Rel')
        self.assertEqual(ex["A.B.C.S"], "structure S where\n  x : Nat\nderiving Repr")
        self.assertEqual(ex["A.B.T"], "inductive T\n| a\n| b")
        self.assertEqual(decls["A.B.f_pos"].keyword, "theorem")
        self.assertEqual(leansrc.signature(LEAN_SAMPLE, decls["A.B.f_pos"]), "theorem f_pos : 0 < f 0 := …")
        self.assertEqual(props.docstring(ex["A.B.f"]), "Doc of `f`.")

    def test_every_declaration_a_property_file_names_is_found(self):
        """Each properties.json names declarations that its files declare, and each card's Lean text
        is a verbatim slice of its file that starts with the declaration's docstring or keyword."""
        paths = sorted(glob.glob(os.path.join(SVGOLF, "tasks", "*", "properties.json")))
        self.assertTrue(paths)
        for path in paths:
            with open(path, encoding="utf-8") as fh:
                info = json.load(fh)
            items = info["properties"] + info["definitions"] + [
                {"decl": info["theorem"], "file": info["file"]}, info["statement"]]
            for it in items:
                with self.subTest(file=os.path.relpath(path, SVGOLF), decl=it["decl"]):
                    text = repo_text(it["file"])
                    d = leansrc.find(text, it["decl"])
                    self.assertIsNotNone(d)
                    ex = leansrc.excerpt(text, d)
                    self.assertIn(ex, text)
                    self.assertRegex(ex.split("\n", 1)[0], r"^(/--|@\[|(private |protected |noncomputable )*"
                                                            r"(def|abbrev|theorem|structure|inductive|class|opaque) )")

    def test_anchored_source_is_the_file(self):
        """The source view's text is the file, byte for byte, with one numbered line per line."""
        files = source_files(".lean") + sorted(glob.glob(os.path.join(LS_ROOT, "LeanModels", "Sv", "*.lean")))
        for p in files:
            with open(p, encoding="utf-8") as fh:
                text = fh.read()
            with self.subTest(file=p):
                out = leansrc.anchored_html(text, leansrc.declarations(text))
                self.assertEqual(strip_tags(out), text)
                self.assertEqual(out.count('class="ln"'), len(text.split("\n")) - (1 if text.endswith("\n") else 0))


class PropsLoadTest(unittest.TestCase):
    """props.load refuses a properties.json that does not match its files."""

    def load(self, edit, lean_edit=lambda text: text):
        task_dir = "svgolf/tasks/add"
        info = json.loads(repo_text(f"{task_dir}/properties.json"))
        edit(info)
        closure = [("tasks.add.Spec", "svgolf/tasks/add/Spec.lean"), ("SvGolf.Task", "svgolf/SvGolf/Task.lean"),
                   ("LeanModels.Sv.Spec2", "LeanModels/Sv/Spec2.lean"),
                   ("LeanModels.Sv.Semantics", "LeanModels/Sv/Semantics.lean"),
                   ("LeanModels.Sv.Sem2", "LeanModels/Sv/Sem2.lean")]

        def read(rel):
            if rel.endswith("properties.json"):
                return json.dumps(info)
            return lean_edit(repo_text(rel)) if rel.endswith("/Properties.lean") else repo_text(rel)
        return props.load("add", task_dir, "SvGolf.Tasks.Add.Statement", closure, read,
                          lambda path, decl: f"x.html#{decl}", lambda rel: os.path.isfile(repo_file(rel)))

    def test_the_shipped_file_loads(self):
        tp = self.load(lambda info: None)
        self.assertEqual([p.name for p in tp.properties][-1], "COMPUTES_SUM")
        self.assertTrue(tp.theorem.signature.startswith("theorem statement_iff_properties"))

    def test_a_missing_declaration_fails(self):
        def edit(info):
            info["properties"][-1]["decl"] += "X"
        with self.assertRaisesRegex(props.PropsError, "declares no"):
            self.load(edit)

    def test_an_untrusted_file_fails(self):
        def edit(info):
            info["definitions"][0]["file"] = "svgolf/tasks/add/reference/add_n.lean"
        with self.assertRaisesRegex(props.PropsError, "neither"):
            self.load(edit)

    def test_a_property_the_theorem_does_not_name_fails(self):
        def lean_edit(text):
            assert " ∧ ComputesSum N (sem N) :=" in text
            return text.replace(" ∧ ComputesSum N (sem N) :=", " :=")
        with self.assertRaisesRegex(props.PropsError, "does not mention the property COMPUTES_SUM"):
            self.load(lambda info: None, lean_edit)

    def test_a_property_outside_properties_lean_fails(self):
        def edit(info):
            info["properties"][-1].update(decl="SvGolf.Tasks.Add.task", file="svgolf/tasks/add/Spec.lean")
        with self.assertRaisesRegex(props.PropsError, "not in svgolf/tasks/add/Properties.lean"):
            self.load(edit)

    def test_a_wrong_statement_fails(self):
        def edit(info):
            info["statement"]["decl"] = "SvGolf.Tasks.Mul.Statement"
        with self.assertRaisesRegex(props.PropsError, "task.json"):
            self.load(edit)


if __name__ == "__main__":
    unittest.main()
