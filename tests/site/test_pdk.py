"""The library selector (decided 2026-11-09: a dropdown on the front page lets the reader see the golf scores on sky130
or on ASAP7): every golf score of the site in two views, sky130 (the default, and the page without
JavaScript) and ASAP7, both ranked when the site is built. Built once with --offline; each page is read as the reader of
each view sees it (pdkview.view_of). The ASAP7 numbers are checked against leaderboard/asap7/<task>.json and the
boards against leaderboard.py's own functions, called here independently of the generator.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)
"""

import contextlib
import html
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
sys.path.insert(0, HERE)
from pdkview import view_of  # noqa: E402


def load(name, path):
    sys.path.insert(0, SITE)
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


build = load("svgolf_site_build_pdk", os.path.join(SITE, "build.py"))
lb = build.lb
combined = lb.combined


def text_of(h):
    return " ".join(html.unescape(re.sub(r"<[^>]+>", " ", h)).split())


def flat(s):
    """Text as `text_of` writes it: every run of whitespace (a number's thin-space groups too) one space."""
    return " ".join(s.split())


def section(page_html, sid):
    """The inner HTML of the element with id `sid` (to its matching close tag, by nesting of the same tag)."""
    m = re.search(r'<(section|div|article|dl)\b[^>]*\bid="' + re.escape(sid) + r'"[^>]*>', page_html)
    if not m:
        raise AssertionError(f"no element with id {sid!r}")
    tag, depth = m.group(1), 1
    for t in re.finditer(r"<(/?)" + tag + r"\b[^>]*>", page_html[m.end():]):
        depth += -1 if t.group(1) else 1
        if depth == 0:
            return page_html[m.end():m.end() + t.start()]
    raise AssertionError(f"<{tag} id={sid!r}> is not closed")


def pinned_flow(task):
    with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
        exp = json.load(fh)
    pin = exp["flow_seq" if lb.task_flow(task) == lb.SEQ_FLOW else "flow"]
    return {"flow": lb.task_flow(task), "yosys": pin["yosys_version"], "canon_script_sha256": pin["canon_script_sha256"],
            "script_sha256": pin["script_sha256"], "ge_table_sha256": pin["ge_table_sha256"]}


class PdkTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            cls.site = build.build_site(offline=True)
        cls.files = cls.site.files
        cls.config = build.load_config()
        cls.listed = [t for t, how in cls.config["tasks"].items() if how != "hidden"]
        cls.records = lb.good_records(lb.load_records(lb.DEFAULT_DATA))
        cls.ident = lb.asap7_identity()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def raw(self, path):
        return self.files[path].decode("utf-8")

    def view(self, path, pdk):
        return view_of(self.raw(path), pdk)

    def task(self, t):
        return lb.load_task(lb.DEFAULT_TASKS, t)

    def boards(self, t):
        """(sky130 board, ASAP7 board) of the players' records of task `t`, from leaderboard.py directly."""
        task = self.task(t)
        mine = [r for r in self.records if r["task"] == t and r["player"] != self.config["reference_player"]]
        flow, statement = pinned_flow(task), lb.current_statement_or_none(task)
        sky = lb.build_board(task, mine, flow=flow, identity=lb.ppa_identity(),
                             input_drive=lb.ppa_setup_now(task).get("input_drive"), statement=statement)
        a7 = lb.build_board(task, mine, flow=flow, statement=statement, pdk="asap7", asap7=lb.load_asap7(t),
                            asap7_identity=self.ident)
        return sky, a7

    def a7_par(self, t):
        """(stem, exact ASAP7 score) of par in the ASAP7 view, from the data: the proved reference with the best ASAP7
        area x time, ties to task.json's order (a reference needs a score at the scoring point, tests/expected.json)."""
        task, table = self.task(t), lb.load_asap7(t)
        with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
            exp = json.load(fh)["tasks"].get(t, {})
        key = lb.point_key(lb.scoring_point(task))
        best = None
        for k, ref in enumerate(task.get("references", [])):
            stem = os.path.splitext(os.path.basename(ref["sv"]))[0]
            if not ((exp.get("references", {}).get(stem) or {}).get("scores") or {}).get(key):
                continue
            e = lb.asap7_entry(table, lb.sha256_file(os.path.join(lb.DEFAULT_TASKS, t, ref["sv"])))
            if e is None:
                continue
            cand = (e["area_e5um2"] * e["time_ps"], k, stem)
            best = cand if best is None or cand < best else best
        return (best[2], best[0]) if best else (None, None)

    # ---- the selector

    def test_every_page_has_the_selector_in_its_header_and_says_what_without_javascript(self):
        for path in sorted(p for p in self.files if p.endswith(".html")):
            h = self.raw(path)
            with self.subTest(page=path):
                head = h[h.index('<header class="site-header">'):h.index("</header>")]
                self.assertRegex(head, r'<div class="pdk-pick" data-pdk-pick hidden><label for="pdk-select">')
                self.assertRegex(head, r'<select id="pdk-select" data-pdk-select autocomplete="off"><option '
                                       r'value="sky130" selected>sky130</option><option value="asap7">ASAP7</option>'
                                       r'</select>')
                self.assertIn("<noscript>", head)
                self.assertIn("the ASAP7 view needs JavaScript", text_of(head))
                # pdk.js in the head, not deferred, before the page is drawn; the other scripts deferred
                self.assertRegex(h[:h.index("</head>")], r'<script src="(\.\./)*pdk\.js"></script>\n<script src="(\.\./)*site\.js" defer>')
        self.assertIn("pdk.js", self.files)
        with open(os.path.join(SITE, "pdk.js"), "rb") as fh:
            self.assertEqual(self.files["pdk.js"], fh.read())

    def test_the_home_page_has_the_dropdown_beside_the_task_cards(self):
        h = self.raw("index.html")
        tasks = h[h.index('id="tasks"'):h.index('<ul class="task-cards">')]
        self.assertIn('<select id="pdk-select-home" data-pdk-select autocomplete="off">', tasks)
        self.assertIn("Golf scores on", text_of(tasks))
        self.assertIn("Seeing them on ASAP7 needs the library selector, which needs JavaScript", text_of(tasks))
        self.assertIn(f'href="rules.html#{build.ASAP7_ANCHOR}"', tasks)

    def test_the_rules_say_how_asap7_is_scored_and_that_sky130_is_the_default(self):
        rules = self.raw("rules.html")
        self.assertIn(f'id="{build.ASAP7_ANCHOR}"', rules)
        part = text_of(rules[rules.index(f'id="{build.ASAP7_ANCHOR}"'):])
        for phrase in ("sky130 is the default", "predictive 7 nm", "never been fabricated", "score/ppa.py --pdk asap7",
                       "read at the grid's floor", "no MUX", "only an inverted output", "leaderboard/asap7/<task>.json"):
            self.assertIn(phrase, part)
        self.assertIn("The ASAP7 view's numbers", text_of(self.raw("reproduce.html")))

    # ---- the two views

    def test_score_pages_carry_both_views_and_each_view_one(self):
        score_pages = ["index.html"] + [p for p in self.files if p.startswith("tasks/") and p.endswith(".html")
                                        and "/properties" not in p and p.count("/") >= 2]
        for path in sorted(score_pages):
            if path.endswith("properties.html"):
                continue
            h = self.raw(path)
            with self.subTest(page=path):
                self.assertIn('class="pdk pdk-sky130"', h)
                self.assertIn('class="pdk pdk-asap7"', h)
                sky, a7 = self.view(path, "sky130"), self.view(path, "asap7")
                self.assertNotIn("pdk-asap7", sky)
                self.assertNotIn("pdk-sky130", a7)
                ids = re.findall(r'(?<![\w-])id="([^"]+)"', h)
                self.assertEqual(len(ids), len(set(ids)), "an id twice: the ASAP7 copy's ids are suffixed")
        # a page without scores has no second view
        for path in ("proving.html", "about.html", "refusals.html"):
            self.assertNotIn('class="pdk pdk-asap7"', self.raw(path))

    def test_the_asap7_view_is_labelled_where_its_numbers_appear(self):
        for path in ["index.html"] + [f"tasks/{t}/index.html" for t in self.listed]:
            with self.subTest(page=path):
                a7, sky = self.view(path, "asap7"), self.view(path, "sky130")
                self.assertIn("Golf scores on ASAP7", text_of(a7))
                self.assertIn("never fabricated", text_of(a7))
                self.assertIn(f"rules.html#{build.ASAP7_ANCHOR}", a7)
                self.assertNotIn("Golf scores on ASAP7", text_of(sky))
        for t in self.listed:
            a7 = self.view(f"tasks/{t}/index.html", "asap7")
            with self.subTest(task=t):
                self.assertIn("Score = area × time: the ASAP7 cell area", text_of(section(a7, "score")))
                self.assertIn("ASAP7 · area × time", text_of(a7))

    def test_the_asap7_boards_are_leaderboards_and_differ_where_the_libraries_do(self):
        for t in self.listed:
            sky, a7 = self.boards(t)
            with self.subTest(task=t):
                self.assertEqual({r["record_hash"] for r in a7["ranking"]}, {r["record_hash"] for r in sky["ranking"]})
                for pdk, board in (("sky130", sky), ("asap7", a7)):
                    lst = section(self.view(f"tasks/{t}/index.html", pdk), "leaderboard")
                    shown = re.findall(r'<a href="records/([0-9a-f]{64})\.html">', lst.split('<ol class="board">', 1)[1]
                                       .split("</ol>", 1)[0])
                    self.assertEqual(shown, [r["record_hash"] for r in board["ranking"]], pdk)
                    for r in board["ranking"]:
                        self.assertIn(flat(combined.fmt(r["um2ns"])), text_of(lst))
        # where the libraries disagree (measured 2026-11-09): on mul, plus-minus-two beats par on sky130 and not on ASAP7
        sky, a7 = self.boards("mul")
        _, par7 = self.a7_par("mul")
        pm2 = {r["player"]: r for r in a7["ranking"]}["plus-minus-two"]
        self.assertGreater(pm2["exact"], par7)
        task = self.task("mul")
        sky_par = lb.par_of(task, [r for r in self.records if r["task"] == "mul"], flow=pinned_flow(task),
                            identity=lb.ppa_identity(), input_drive=lb.ppa_setup_now(task).get("input_drive"),
                            statement=lb.current_statement_or_none(task))
        self.assertLess({r["player"]: r for r in sky["ranking"]}["plus-minus-two"]["exact"], sky_par["exact"])

    def test_par_record_and_under_par_in_both_views(self):
        for t in self.listed:
            stem, exact = self.a7_par(t)
            sky, a7 = self.boards(t)
            with self.subTest(task=t):
                head = text_of(section(self.view(f"tasks/{t}/index.html", "asap7"), "numbers"))
                self.assertIn(flat(f"{combined.fmt(combined.um2ns(exact, 'asap7'))} µm²·ns {stem}"), head)
                best = min([exact] + [r["exact"] for r in a7["ranking"]])
                self.assertIn(flat(combined.fmt(combined.um2ns(best, "asap7"))), head)
                pct = round((exact - best) * 100 / exact)
                self.assertIn("0%" if pct == 0 else f"−{pct}%", head)
                card = self.view("index.html", "asap7")
                card = card[card.index(f"<code>{t}</code>"):]
                card = card[:card.index("</li>")]
                self.assertIn(flat(combined.fmt(combined.um2ns(exact, "asap7"))), text_of(card))
                # the sky130 view keeps the sky130 numbers
                self.assertNotIn(flat(f"{combined.fmt(combined.um2ns(exact, 'asap7'))} µm²·ns {stem}"),
                                 text_of(section(self.view(f"tasks/{t}/index.html", "sky130"), "numbers")))
        # add: the record of the ASAP7 view is par (select-six does not beat add_n there), unlike on sky130
        h7 = text_of(section(self.view("tasks/add/index.html", "asap7"), "numbers"))
        h1 = text_of(section(self.view("tasks/add/index.html", "sky130"), "numbers"))
        self.assertIn("0%", h7)
        self.assertNotIn("select-six", h7)
        self.assertIn("select-six", h1)

    def test_the_asap7_explorer_and_score_chart_draw_the_asap7_numbers(self):
        for t in self.listed:
            a7 = self.raw(f"tasks/{t}/index.html")
            m = re.search(r'<script type="application/json" id="task-data-asap7">(.*?)</script>', a7, re.S)
            with self.subTest(task=t):
                self.assertIsNotNone(m)
                data = json.loads(m.group(1))
                self.assertNotIn("points", data)            # the scoring point only
                self.assertNotIn("scaling", data)
                self.assertFalse({"energy_fj", "energy_cycle_fj", "leakage_nw"} & {x["key"] for x in data["metrics"]})
                area = next(x for x in data["metrics"] if x["key"] == "area_um2")
                self.assertIn("ASAP7", area["what"])
                table = lb.load_asap7(t)
                by_sha = {e["sv_sha256"]: e for e in table["designs"]}
                stem, _ = self.a7_par(t)
                for d in data["designs"]:
                    if "adp" not in d["m"]:
                        continue
                    e = by_sha[lb.sha256_file(self.design_file(t, d))]
                    self.assertEqual(d["m"]["area_um2"], e["area_e5um2"] / 100000)
                    self.assertEqual(d["m"]["time_ps"], e["time_ps"])
                    self.assertEqual(d["m"]["adp"], e["area_e5um2"] * e["time_ps"] / 1e8)
                self.assertEqual([d["name"] for d in data["designs"] if d["par"]], [stem] if stem else [])
                score = section(view_of(a7, "asap7"), "score")
                if stem:
                    self.assertEqual(score.count('data-scale="linear"'), 2)
                    self.assertIn('class="par-line"', score)

    def design_file(self, t, d):
        if d["kind"] == "reference":
            ref = next(r for r in self.task(t)["references"]
                       if os.path.splitext(os.path.basename(r["sv"]))[0] == d["name"])
            return os.path.join(lb.DEFAULT_TASKS, t, ref["sv"])
        if d["kind"] == "baseline":
            with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
                e = json.load(fh)["tasks"][t]["baselines"][d["name"]]
            return os.path.join(SVGOLF, "tests", t, e.get("sv", f"baselines/{d['name']}.sv"))
        return os.path.join(lb.DEFAULT_DATA, t, d["id"] + ".sv")

    def test_every_detail_page_shows_its_entry_in_the_asap7_view(self):
        for rec in self.records:
            t = rec["task"]
            if t not in self.listed:
                continue
            path = f"tasks/{t}/records/{rec['record_hash']}.html"
            e = lb.asap7_entry(lb.load_asap7(t), rec["files"]["sv"]["sha256"])
            with self.subTest(page=path):
                self.assertIsNotNone(e)
                dash = text_of(section(self.view(path, "asap7"), "dashboard"))
                self.assertIn(flat(f"{build.grouped(lb.fmt_um2_e5(e['area_e5um2']))} µm² exactly"), dash)
                self.assertIn(flat(f"{build.thin(e['time_ps'])} ps"), dash)
                self.assertIn(flat(combined.fmt(combined.um2ns(e["area_e5um2"] * e["time_ps"], "asap7"))), dash)
                rep = text_of(section(self.view(path, "asap7"), "reproduce"))
                self.assertIn("--pdk asap7", rep)
                self.assertIn(str(e["area_e5um2"]), rep)
                sky = text_of(section(self.view(path, "sky130"), "dashboard"))
                self.assertNotIn(flat(f"{build.grouped(lb.fmt_um2_e5(e['area_e5um2']))} µm² exactly"), sky)

    def test_the_references_and_baselines_tables_mark_par_per_view(self):
        for t in self.listed:
            stem, exact = self.a7_par(t)
            h = self.raw(f"tasks/{t}/index.html")
            refs = section(h, "references")
            with self.subTest(task=t):
                if stem:
                    row = re.search(r'<tr class="([^"]*)" id="ref-' + re.escape(stem) + '"', refs)
                    self.assertIsNotNone(row)
                    self.assertIn("par-a7", row.group(1).split())
                    a7 = section(self.view(f"tasks/{t}/index.html", "asap7"), "references")
                    self.assertIn(flat(combined.fmt(combined.um2ns(exact, "asap7"))), text_of(a7))
                self.assertEqual(len(re.findall(r'class="[^"]*\bpar-a7\b', refs)), 1 if stem else 0)

    def test_the_machine_outputs_carry_both_views(self):
        summary = json.loads(self.files["data/site.json"])
        for x in summary["tasks"]:
            with self.subTest(task=x["name"]):
                self.assertEqual(x["ranked_axes"], ["area_um2_sky130", "time_ps"])
                self.assertEqual(x["asap7"]["ranked_axes"], ["area_um2_asap7", "time_ps"])
                stem, _ = self.a7_par(x["name"])
                self.assertEqual((x["asap7"]["par"] or {}).get("design"), stem)
                data = json.loads(self.files[f"data/tasks/{x['name']}.json"])
                sky, a7 = self.boards(x["name"])
                self.assertEqual([r["record_hash"] for r in data["asap7"]["submissions_board"]["ranking"]],
                                 [r["record_hash"] for r in a7["ranking"]])
                self.assertEqual(data["asap7"]["submissions_board"]["pdk"], "asap7")
                self.assertEqual(data["submissions_board"]["pdk"], "sky130")

    def test_the_task_text_says_it_quotes_sky130_numbers_in_the_asap7_view(self):
        """The task section's text (content/tasks/<t>.md) quotes sky130's area, time and score and compares designs by
        them; the ASAP7 view says so above it (a review finding, 2026-11-09), the sky130 view does not. GE and depth
        are the same on either library, so a text quoting only them needs no note."""
        note = "This text quotes sky130 numbers"
        for t in self.listed:
            with open(os.path.join(SITE, "content", "tasks", f"{t}.md"), encoding="utf-8") as fh:
                raw = fh.read()
            quotes = bool(re.search(r"\{\{\s*[A-Za-z0-9_]+\.(area|time|score)\s*\}\}", raw))
            with self.subTest(task=t):
                a7 = text_of(section(self.view(f"tasks/{t}/index.html", "asap7"), "statement"))
                sky = text_of(section(self.view(f"tasks/{t}/index.html", "sky130"), "statement"))
                self.assertEqual(note in a7, quotes)
                self.assertNotIn(note, sky)
        self.assertIn(note, text_of(section(self.view("tasks/add/index.html", "asap7"), "statement")))

    def test_par_sits_in_its_place_on_each_board_and_the_lead_beats_par(self):
        """The leaderboard list puts par's row under the records that beat par and above the rest, in both views; the
        first record is highlighted as the lead only when it beats par (on ASAP7's add board select-six does not:
        the record there is par)."""
        for t in self.listed:
            sky, a7 = self.boards(t)
            task = self.task(t)
            sky_par = lb.par_of(task, [r for r in self.records if r["task"] == t], flow=pinned_flow(task),
                                identity=lb.ppa_identity(), input_drive=lb.ppa_setup_now(task).get("input_drive"),
                                statement=lb.current_statement_or_none(task))
            pars = {"sky130": sky_par["exact"] if sky_par else None, "asap7": self.a7_par(t)[1]}
            for pdk, board in (("sky130", sky), ("asap7", a7)):
                lst = section(self.view(f"tasks/{t}/index.html", pdk), "leaderboard")
                ol = lst.split('<ol class="board">', 1)[1].split("</ol>", 1)[0]
                rows = re.findall(r'<li(?: class="(lead|par)")?>(.*?)</li>', ol, re.S)
                kinds = [("par" if k == "par" else "record", k == "lead") for k, _ in rows]
                with self.subTest(task=t, pdk=pdk):
                    par_exact = pars[pdk]
                    if not any(k == "par" for k, _ in kinds):
                        continue
                    if par_exact is None:
                        self.assertEqual(kinds[-1][0], "par")
                        continue
                    above = sum(1 for r in board["ranking"] if r["exact"] < par_exact)
                    self.assertEqual([k for k, _ in kinds].index("par"), above, [k for k, _ in kinds])
                    first = board["ranking"][0] if board["ranking"] else None
                    leads = [lead for _, lead in kinds if lead]
                    self.assertEqual(len(leads), 1 if first and first["exact"] < par_exact else 0)
        rows = re.findall(r'<li(?: class="(lead|par)")?>', section(self.view("tasks/add/index.html", "asap7"),
                                                                   "leaderboard"))
        self.assertEqual(rows[0], "par")
        self.assertNotIn("lead", rows)

    def test_a_reference_players_record_says_par_only_where_it_is_par(self):
        """A record of the reference player calls itself par in a view only when its reference is that view's par;
        the others are shown with par (before 2026-11-09 mul_n_byhand, sbox_table and the fdivp ones said par)."""
        summary = {x["name"]: x for x in json.loads(self.files["data/site.json"])["tasks"]}
        seen = {"par": 0, "not": 0}
        for rec in self.records:
            t = rec["task"]
            if t not in self.listed or rec["player"] != self.config["reference_player"]:
                continue
            task = self.task(t)
            # the reference by its design AND its proof (add_n_byhand is add_n's design with another proof)
            stem = next((os.path.splitext(os.path.basename(r["sv"]))[0] for r in task.get("references", [])
                         if lb.sha256_file(os.path.join(lb.DEFAULT_TASKS, t, r["sv"])) == rec["files"]["sv"]["sha256"]
                         and lb.sha256_file(os.path.join(lb.DEFAULT_TASKS, t, r["lean"]))
                         == rec["files"]["lean"]["sha256"]), None)
            path = f"tasks/{t}/records/{rec['record_hash']}.html"
            for pdk, par in (("sky130", (summary[t].get("par") or {}).get("design")),
                             ("asap7", ((summary[t].get("asap7") or {}).get("par") or {}).get("design"))):
                head = text_of(self.view(path, pdk).split('id="dashboard"', 1)[0])
                with self.subTest(page=path, pdk=pdk):
                    if stem is not None and stem == par:
                        seen["par"] += 1
                        self.assertIn("It is par, the bar to beat", head)
                        self.assertIn("reference: par, not an entry", head)
                    else:
                        seen["not"] += 1
                        self.assertIn("It is shown with par", head)
                        self.assertNotIn("It is par", head)
                        self.assertIn("reference: not an entry", head)
        self.assertTrue(seen["par"] and seen["not"], seen)

    def test_the_home_selector_may_shrink_on_a_phone(self):
        """The home page's selector block sits in the course head's flex line; the rule that keeps the heading at its
        width must not keep it at its one-line width (2026-11-09: the front page scrolled sideways on a phone)."""
        with open(os.path.join(SITE, "style.css"), encoding="utf-8") as fh:
            css = fh.read()
        rule = re.search(r"\.course > \.section-head > \.pdk-home \{([^}]*)\}", css)
        self.assertIsNotNone(rule)
        self.assertIn("min-width: 0", rule.group(1))
        self.assertRegex(rule.group(1), r"flex: 1 1 auto")
        self.assertGreater(rule.start(), css.index(".course > .section-head > div {"))

    def test_a_design_without_a_bound_asap7_entry_is_a_build_warning(self):
        """`asap7_gaps`: a design the ASAP7 view would show without a bound entry, or a task without its file, is a
        warning of the build (fatal under --strict), so that a publish build never ships a partial view (a review
        finding, 2026-11-09). The committed files have none."""
        self.assertFalse([w for w in self.site.warnings if "ASAP7" in w or "asap7" in w], self.site.warnings)

        class Fake:
            def __init__(self):
                self.warnings, self.a7_identity = [], lb.asap7_identity()

            def warn(self, msg):
                self.warnings.append(msg)

        with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
            expected = json.load(fh)
        for name in ("add", "arbiter"):
            t = build.Task(name, self.task(name), "listed")
            t.records = [r for r in self.records if r["task"] == name]
            t.flow = pinned_flow(t.task)
            table = lb.load_asap7(name)
            fake = Fake()
            build.asap7_gaps(fake, t, table, expected)
            self.assertEqual(fake.warnings, [], name)
            # one record's entry gone
            rec = next(r for r in t.records if r["player"] != self.config["reference_player"]) \
                if name == "add" else t.records[0]
            cut = dict(table, designs=[e for e in table["designs"] if e["sv_sha256"] != rec["files"]["sv"]["sha256"]])
            fake = Fake()
            build.asap7_gaps(fake, t, cut, expected)
            self.assertEqual(len(fake.warnings), 1, fake.warnings)
            self.assertIn(rec["record_hash"][:12], fake.warnings[0])
            self.assertIn("asap7 --write", fake.warnings[0])
        # the task's whole file gone
        t = build.Task("arbiter", self.task("arbiter"), "listed")
        t.records, t.flow = [r for r in self.records if r["task"] == "arbiter"], pinned_flow(self.task("arbiter"))
        fake = Fake()
        with tempfile.TemporaryDirectory() as empty:
            real = lb.ASAP7_DIR
            try:
                lb.ASAP7_DIR = empty
                build.asap7_gaps(fake, t, None, expected)
            finally:
                lb.ASAP7_DIR = real
        self.assertEqual(len(fake.warnings), 1, fake.warnings)
        self.assertIn("no leaderboard/asap7/arbiter.json", fake.warnings[0])

    def test_the_sky130_view_is_the_page_without_the_selector(self):
        """The default view shows the sky130 numbers exactly where they were: the sky130 board's numbers and par's
        sky130 score are in it, and no ASAP7 score is."""
        for t in self.listed:
            sky, a7 = self.boards(t)
            page = text_of(self.view(f"tasks/{t}/index.html", "sky130"))
            with self.subTest(task=t):
                for r in sky["ranking"]:
                    self.assertIn(flat(combined.fmt(r["um2ns"])), page)
                self.assertNotIn("ASAP7 · area × time", page)
                self.assertNotIn("Score = area × time: the ASAP7", page)



class PdkScriptTest(unittest.TestCase):
    """site/pdk.js under a fake DOM (tests/site/pdkjs_check.js; needs node, else skipped): the URL first, then the
    stored choice, then sky130; storage that throws tolerated; the choice stored and in the URL; page links carry it."""

    def test_the_selector_script(self):
        node = shutil.which("node")
        if not node:
            self.skipTest("node is not installed")
        proc = subprocess.run([node, os.path.join(HERE, "pdkjs_check.js"), os.path.join(SITE, "pdk.js")],
                              capture_output=True, text=True, timeout=60)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("all ok", proc.stdout)


if __name__ == "__main__":
    unittest.main()
