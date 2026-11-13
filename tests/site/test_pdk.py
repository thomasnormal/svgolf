"""The course selector (decided 2026-11-09: a dropdown on the front page lets the reader choose the course; 2026-11-11/12:
its courses are sky130 and ASAP7 placed and routed, `asap7pnr`): every golf score of the site in two views, sky130 (the
default, and the page without JavaScript) and the routed course, both ranked when the site is built. Built once with
--offline; each page is read as the reader of each view sees it (pdkview.view_of). The routed numbers are checked
against leaderboard/asap7pnr/<task>.json's BOUND entries (a design without one shows no number) and the boards against
leaderboard.py's own functions, called here independently of the generator.

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


R = "asap7pnr"                    # the routed course's value (the selector's second course since 2026-11-12)


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
        cls.pins = lb.asap7pnr_identity()

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def raw(self, path):
        return self.files[path].decode("utf-8")

    def view(self, path, pdk):
        return view_of(self.raw(path), pdk)

    def task(self, t):
        return lb.load_task(lb.DEFAULT_TASKS, t)

    def bound(self, t, sha):
        """The BOUND routed entry of the design file `sha` of task `t` (its ASAP7 view entry's netlists, the current
        view and pins, a valid scoring run), or None: from the files, by leaderboard.py's rule."""
        status, _why, e = lb.asap7pnr_status(lb.load_asap7pnr(t), lb.load_asap7(t), sha, task=self.task(t),
                                             pins=self.pins)
        return e if status == "bound" else None

    def boards(self, t):
        """(sky130 board, routed board) of the players' records of task `t`, from leaderboard.py directly."""
        task = self.task(t)
        mine = [r for r in self.records if r["task"] == t and r["player"] != self.config["reference_player"]]
        flow, statement = pinned_flow(task), lb.current_statement_or_none(task)
        sky = lb.build_board(task, mine, flow=flow, identity=lb.ppa_identity(),
                             input_drive=lb.ppa_setup_now(task).get("input_drive"), statement=statement)
        a7 = lb.build_board(task, mine, flow=flow, statement=statement, pdk=R, asap7=lb.load_asap7(t),
                            asap7_identity=self.ident, asap7pnr=lb.load_asap7pnr(t), pnr_identity=self.pins)
        return sky, a7

    def a7_par(self, t):
        """(stem, exact routed score) of par on the routed course, from the data: par's design (decided 2026-11-12:
        one design per task, leaderboard/par.json), the same design as sky130's, with its BOUND routed entry (it needs a
        score at the scoring point, tests/expected.json); (None, None) without one."""
        task = self.task(t)
        with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
            exp = json.load(fh)["tasks"].get(t, {})
        key = lb.point_key(lb.scoring_point(task))
        stem = lb.par_stem(lb.DEFAULT_TASKS, task)
        ref = next((r for r in task.get("references", []) if os.path.splitext(os.path.basename(r["sv"]))[0] == stem),
                   None)
        if ref is None or not ((exp.get("references", {}).get(stem) or {}).get("scores") or {}).get(key):
            return None, None
        e = self.bound(t, lb.sha256_file(os.path.join(lb.DEFAULT_TASKS, t, ref["sv"])))
        return (stem, e["scores"]["v_owner"]["exact"]) if e is not None else (None, None)

    # ---- the selector

    def test_every_page_has_the_selector_in_its_header_and_says_what_without_javascript(self):
        """Every page but the front page and the 404 page carries the course selector, "Course", in its header
        (2026-11-11: the front page has its own control, "The course", beside its task cards, and no second one;
        2026-11-12: the 404 page shows no scores). Its courses (2026-11-12): sky130 and ASAP7 · placed and routed."""
        for path in sorted(p for p in self.files if p.endswith(".html")):
            h = self.raw(path)
            with self.subTest(page=path):
                head = h[h.index('<header class="site-header">'):h.index("</header>")]
                # pdk.js in the head, not deferred, before the page is drawn; the other scripts deferred
                self.assertRegex(h[:h.index("</head>")], r'<script src="(\.\./)*pdk\.js"></script>\n<script src="(\.\./)*site\.js" defer>')
                if path in ("index.html", "404.html"):
                    self.assertNotIn("pdk-select", head)
                    continue
                self.assertRegex(head, r'<div class="pdk-pick" data-pdk-pick hidden><label for="pdk-select">Course')
                self.assertRegex(head, r'<select id="pdk-select" data-pdk-select autocomplete="off"><option '
                                       r'value="sky130" selected>sky130</option><option value="asap7pnr">ASAP7 · placed '
                                       r'and routed</option></select>')
                self.assertNotIn('value="asap7"', head)
                self.assertIn("<noscript>", head)
                self.assertIn("the routed ASAP7 course needs JavaScript", text_of(head))
        self.assertIn("pdk.js", self.files)
        with open(os.path.join(SITE, "pdk.js"), "rb") as fh:
            self.assertEqual(self.files["pdk.js"], fh.read())

    def test_the_home_page_has_the_dropdown_beside_the_task_cards(self):
        """The front page's course control (2026-11-11): the kicker "The course" is the select's label, its options
        sky130 and ASAP7 · placed and routed (2026-11-12); without JavaScript the scores are sky130's and a line says
        so; the routed course's helper line links how it is scored."""
        h = self.raw("index.html")
        tasks = h[h.index('id="tasks"'):h.index('<ul class="task-cards">')]
        self.assertIn('<label class="label label-accent" for="pdk-select-home">The course</label>', tasks)
        self.assertIn('<select id="pdk-select-home" data-pdk-select autocomplete="off"><option value="sky130" '
                      'selected>sky130</option><option value="asap7pnr">ASAP7 · placed and routed</option></select>',
                      tasks)
        self.assertIn("The scores are on sky130; the course ASAP7 · placed and routed needs JavaScript.",
                      text_of(tasks))
        self.assertIn(f'href="rules.html#{build.ASAP7PNR_ANCHOR}"', tasks)

    def test_the_rules_say_how_asap7_is_scored_and_that_sky130_is_the_default(self):
        """The cells-only ASAP7 view's section stays (it is the routed course's input and a column of its record
        pages)."""
        rules = self.raw("rules.html")
        self.assertIn(f'id="{build.ASAP7_ANCHOR}"', rules)
        part = text_of(rules[rules.index(f'id="{build.ASAP7_ANCHOR}"'):rules.index(f'id="{build.ASAP7PNR_ANCHOR}"')])
        for phrase in ("sky130 is the default", "predictive 7 nm", "never been fabricated", "score/ppa.py --pdk asap7",
                       "read at the grid's floor", "no MUX", "only an inverted output", "leaderboard/asap7/<task>.json",
                       "cells only (A0′)"):
            self.assertIn(phrase, part)
        self.assertIn("The ASAP7 view's numbers", text_of(self.raw("reproduce.html")))

    def test_the_rules_say_how_the_routed_course_is_scored(self):
        """The rules page's section "How the routed course is scored" (2026-11-12): the flow and its pins, the score,
        the seed rule, what a run must pass, what the equivalence check shows and the negative control of 2026-11-13
        (said exactly: the flow compares the routed netlist with its own input, the sha256 binding ties that input to
        the design, the control is not a step of every run), what is not checked or not done, what a record not routed
        yet shows, the pictures, and where the files are; the routed course's pages link it."""
        rules = self.raw("rules.html")
        self.assertIn(f'id="{build.ASAP7PNR_ANCHOR}"', rules)
        part = " ".join(text_of(rules[rules.index(f'id="{build.ASAP7PNR_ANCHOR}"'):].split("<h2", 1)[0]).split())
        for phrase in ("How the routed course is scored", "?pdk=asap7pnr", "?pdk=asap7", "OpenROAD-flow-scripts",
                       "score/pnr/pins.json", "min_v1", "Score = area x time", "the clock period minus the worst setup "
                       "slack, with the wires extracted from the layout", "One run, one seed",
                       "the seed its submission names, else a seed drawn at random once",
                       "Every design routed so far (2026-11-11 to 2026-11-13) ran at seed 1",
                       "leaderboard.py add does not take a seed yet",
                       "The flow's equivalence check compares the routed netlist with the netlist the run was given: it "
                       "shows that place and route preserved the run's input, not that the input was the design's "
                       "netlist", "That the input is the design's ASAP7 netlist is checked by sha256",
                       "A negative control was run on 2026-11-13", "Circuits are DIFFERENT", "(4 of 4)",
                       "The tool exits 0 either way; its verdict is read from its log, as the flow does",
                       "This control is not a pinned step of every run", "Hold timing, other corners, and power are not "
                       "scored", "not yet made again from the repository alone", "slow-signal (max-slew) warnings",
                       "not routed yet: place and route pending", "Since 2026-11-13 every design the tasks show",
                       "leaderboard/asap7pnr/<task>.json", "site/layouts/<task>/",
                       "a predictive library at one corner, not sign-off"):
            self.assertIn(phrase, part)
        self.assertNotIn("not yet checked by a negative control", part)
        for p in ["index.html"] + [f"tasks/{t}/index.html" for t in self.listed]:
            with self.subTest(page=p):
                self.assertIn(f"rules.html#{build.ASAP7PNR_ANCHOR}", self.view(p, R))

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
                self.assertIn(f'class="pdk pdk-{R}"', h)
                self.assertNotIn('pdk-asap7"', h)                 # the old view's class is gone
                sky, a7 = self.view(path, "sky130"), self.view(path, R)
                self.assertNotIn(f"pdk-{R}", sky)
                self.assertNotIn("pdk-sky130", a7)
                ids = re.findall(r'(?<![\w-])id="([^"]+)"', h)
                self.assertEqual(len(ids), len(set(ids)), "an id twice: the routed copy's ids are suffixed")
        # a page without scores has no second view
        for path in ("proving.html", "about.html", "refusals.html"):
            self.assertNotIn(f'class="pdk pdk-{R}"', self.raw(path))

    def test_the_routed_course_is_labelled_where_its_numbers_appear(self):
        for path in ["index.html"] + [f"tasks/{t}/index.html" for t in self.listed]:
            with self.subTest(page=path):
                a7, sky = self.view(path, R), self.view(path, "sky130")
                self.assertIn("Golf scores on ASAP7, placed and routed", text_of(a7))
                self.assertIn("never fabricated", text_of(a7))
                self.assertIn(f"rules.html#{build.ASAP7PNR_ANCHOR}", a7)
                self.assertNotIn("Golf scores on ASAP7", text_of(sky))
        for t in self.listed:
            a7 = self.view(f"tasks/{t}/index.html", R)
            with self.subTest(task=t):
                self.assertIn("Score = area × time on ASAP7 placed and routed", text_of(section(a7, "score")))
                self.assertIn("ASAP7 routed · area × time", text_of(a7))

    def test_an_old_asap7_link_is_told_what_changed(self):
        """An old ?pdk=asap7 link or stored choice (the cells-only view the routed course replaced, 2026-11-12) shows
        the routed course, and the banner of every page with scores carries the notice pdk.js reveals for it
        (`html[data-pdk-moved]`, tests/site/pdkjs_check.js); hidden otherwise. The routed numbers are never shown under
        the old name without it."""
        with open(os.path.join(SITE, "style.css"), encoding="utf-8") as fh:
            css = fh.read()
        self.assertIn(".pdk-moved-note { display: none; }", css)
        self.assertIn("html[data-pdk-moved] .pdk-moved-note { display: inline; }", css)
        for path in ["index.html"] + [f"tasks/{t}/index.html" for t in self.listed]:
            with self.subTest(page=path):
                banner = re.search(rf'<div class="pdk-{R} pdk-banner"><p><span class="pdk-moved-note">(.*?)</span>',
                                   self.raw(path), re.S)
                self.assertIsNotNone(banner)
                self.assertEqual(text_of(banner.group(1)), build.PNR_MOVED)

    def test_how_to_submit_says_its_commands_print_sky130_numbers_on_the_routed_course(self):
        """On the routed course a task's par is a routed number while How to submit's commands print sky130's
        (2026-11-11/12): a line right above the commands says so, and that the routed numbers come from one run made
        after the record; the sky130 course has no such line."""
        line = ("The commands print sky130 numbers; a record's routed ASAP7 numbers come from one place-and-route run "
                "made after it is recorded")
        for t in self.listed:
            with self.subTest(task=t):
                a7, sky = section(self.view(f"tasks/{t}/index.html", R), "submit"), \
                    section(self.view(f"tasks/{t}/index.html", "sky130"), "submit")
                self.assertEqual(text_of(a7).count(line), 1)
                self.assertNotIn(line, text_of(sky))
                at = a7.index("The commands print sky130 numbers")
                self.assertRegex(a7[at:], r"^[^<]*(<a [^>]*>[^<]*</a>[^<]*)*</p>\s*<div class=\"codebox")
                self.assertIn(f'href="../../rules.html#{build.ASAP7PNR_ANCHOR}">how the routed course is scored</a>',
                              a7[at:].split("</p>", 1)[0])
                self.assertIn("leaderboard.py add", a7[at:].split("</pre>", 1)[0])

    def test_each_course_says_what_it_counts(self):
        """The two courses (2026-11-11/12): sky130 counts the cells only (no wires, no place and route), the routed
        course places and routes each design and counts the wires; each says so where it is chosen (the front page's
        helper line and its closed note above the cards) and, on the routed course, in the banner of every page that
        shows golf scores."""
        h = self.raw("index.html")
        head = h[h.index('id="tasks"'):h.index('<ul class="task-cards">')]
        notes = re.findall(r'<details class="note course-note-fold"><summary>(.*?)</summary>\s*<p class="course-note">',
                           head)
        self.assertEqual(notes, ["What the score, Par, Record and Under par mean"])
        for pdk in ("sky130", R):
            with self.subTest(view=pdk):
                v = self.view("index.html", pdk)
                course = text_of(v[v.index('id="tasks"'):v.index('<ul class="task-cards">')])
                what = text_of(re.search(r'<p class="pdk-what[^"]*">(.*?)</p>', v, re.S).group(1))
                note = text_of(re.search(r'<p class="course-note">(.*?)</p>', v, re.S).group(1))
                self.assertIn("par while no submission beats it", note)
                self.assertNotIn("never fabricated", note)      # said once: in the banner
                if pdk == "sky130":
                    self.assertIn("no wires, no place and route", what)
                    self.assertIn("the default course", what)
                    self.assertIn("it counts the cells only: no wires, no place and route", note)
                else:
                    self.assertIn("each design placed and routed by OpenROAD, wires included", what)
                    self.assertIn("the wires count", note)
                    self.assertNotIn("no place and route", what + note)
                self.assertEqual("<strong>Golf scores on ASAP7, placed and routed</strong>" in v, pdk == R)
                self.assertNotIn("Golf scores on", course)          # the old label of the control
        for path in ["index.html"] + [f"tasks/{t}/index.html" for t in self.listed]:
            with self.subTest(page=path):
                banner = re.search(rf'<div class="pdk-{R} pdk-banner">(.*?)</div>', self.raw(path), re.S)
                self.assertIsNotNone(banner)
                self.assertIn("each design placed and routed by OpenROAD, wires included. A design not routed yet shows "
                              "a dash.", text_of(banner.group(1)))

    def test_the_routed_boards_are_leaderboards_of_the_bound_records(self):
        """Each routed board ranks exactly the records with a bound routed entry, by their routed score; every other
        sky130-ranked record is listed under "Not ranked" with its reason (not routed yet), with no routed number."""
        for t in self.listed:
            sky, a7 = self.boards(t)
            recs = {r["record_hash"]: r for r in self.records}
            with self.subTest(task=t):
                bound = {h for h in (r["record_hash"] for r in sky["ranking"])
                         if self.bound(t, recs[h]["files"]["sv"]["sha256"]) is not None}
                self.assertEqual({r["record_hash"] for r in a7["ranking"]}, bound)
                for r in a7["unranked"]:
                    self.assertIsNone(r["exact"])
                    self.assertIsNone(r["area_e5um2"])
                    self.assertTrue(r["reason"])
                for pdk, board in (("sky130", sky), (R, a7)):
                    lst = section(self.view(f"tasks/{t}/index.html", pdk), "leaderboard")
                    shown = re.findall(r'<a href="records/([0-9a-f]{64})\.html">', lst.split('<ol class="board">', 1)[1]
                                       .split("</ol>", 1)[0])
                    self.assertEqual(shown, [r["record_hash"] for r in board["ranking"]], pdk)
                    for r in board["ranking"]:
                        self.assertIn(flat(combined.fmt(r["um2ns"])), text_of(lst))
                not_ranked = section(self.view(f"tasks/{t}/index.html", R), "leaderboard")
                for r in a7["unranked"]:
                    self.assertIn(r["record_hash"], not_ranked)
                    self.assertIn(r["reason"], text_of(not_ranked))
        # where the courses disagree: on add, select-six beats par on sky130 and not on the routed course
        sky, a7 = self.boards("add")
        _, par7 = self.a7_par("add")
        s6 = {r["player"]: r for r in a7["ranking"]}["select-six"]
        self.assertGreater(s6["exact"], par7)
        task = self.task("add")
        sky_par = lb.par_of(task, [r for r in self.records if r["task"] == "add"], flow=pinned_flow(task),
                            identity=lb.ppa_identity(), input_drive=lb.ppa_setup_now(task).get("input_drive"),
                            statement=lb.current_statement_or_none(task),
                            names=lb.par_names(lb.DEFAULT_TASKS, task))
        self.assertLess({r["player"]: r for r in sky["ranking"]}["select-six"]["exact"], sky_par["exact"])
        # a record not routed yet (every add design is routed since 2026-11-13; here a copy of add's routed table
        # without fernladder's Sklansky adder): on the sky130 board, not on the routed one, listed under "Not ranked"
        # with the reason and no routed number
        mine = [r for r in self.records if r["task"] == "add" and r["player"] != self.config["reference_player"]]
        skl = next(r for r in mine if r["record_hash"].startswith("f5ecef0e"))
        pnr = lb.load_asap7pnr("add")
        cut = dict(pnr, designs=[e for e in pnr["designs"] if e["sv_sha256"] != skl["files"]["sv"]["sha256"]])
        a7cut = lb.build_board(task, mine, flow=pinned_flow(task), statement=lb.current_statement_or_none(task), pdk=R,
                               asap7=lb.load_asap7("add"), asap7_identity=self.ident, asap7pnr=cut,
                               pnr_identity=self.pins)
        self.assertIn(skl["record_hash"], {r["record_hash"] for r in sky["ranking"]})
        self.assertIn(skl["record_hash"], {r["record_hash"] for r in a7["ranking"]})
        self.assertNotIn(skl["record_hash"], {r["record_hash"] for r in a7cut["ranking"]})
        (row,) = [r for r in a7cut["unranked"] if r["record_hash"] == skl["record_hash"]]
        self.assertEqual((row["reason"], row["exact"], row["area_e5um2"], row["time_ps"]),
                         ("not routed yet: place and route pending", None, None, None))

    def test_par_record_and_under_par_in_both_views(self):
        for t in self.listed:
            stem, exact = self.a7_par(t)
            sky, a7 = self.boards(t)
            with self.subTest(task=t):
                head = text_of(section(self.view(f"tasks/{t}/index.html", R), "numbers"))
                self.assertIsNotNone(stem)             # every par design is routed today (2026-11-13)
                self.assertIn(flat(f"{combined.fmt(combined.um2ns(exact, R))} µm²·ns {stem}"), head)
                best = min([exact] + [r["exact"] for r in a7["ranking"]])
                self.assertIn(flat(combined.fmt(combined.um2ns(best, R))), head)
                pct = round((exact - best) * 100 / exact)
                self.assertIn("0%" if pct == 0 else f"{pct}%", head)       # no minus sign (2026-11-11)
                self.assertNotIn("−", head)
                cards = self.view("index.html", R).split('<li class="task-card">')[1:]
                (card,) = [c.split("</li>", 1)[0] for c in cards if f'href="tasks/{t}/index.html"' in c.split("</li>", 1)[0]]
                self.assertIn(flat(combined.fmt(combined.um2ns(exact, R))), text_of(card))
                # the sky130 view keeps the sky130 numbers
                self.assertNotIn(flat(f"{combined.fmt(combined.um2ns(exact, R))} µm²·ns {stem}"),
                                 text_of(section(self.view(f"tasks/{t}/index.html", "sky130"), "numbers")))
        # add: the two courses name different records. On sky130 it is select-six; on the routed course (every add
        # design routed since 2026-11-13) fernladder's Sklansky adder, 2% under par add_n (select-six is 1.6% over it)
        h7 = text_of(section(self.view("tasks/add/index.html", R), "numbers"))
        h1 = text_of(section(self.view("tasks/add/index.html", "sky130"), "numbers"))
        self.assertIn("fernladder", h7)
        self.assertIn("Under par 2%", h7)
        self.assertNotIn("select-six", h7)
        self.assertEqual(h7.count("add_n"), 1)            # par only
        self.assertIn("select-six", h1)

    def test_the_routed_explorer_and_score_chart_draw_the_routed_numbers(self):
        for t in self.listed:
            a7 = self.raw(f"tasks/{t}/index.html")
            m = re.search(rf'<script type="application/json" id="task-data-{R}">(.*?)</script>', a7, re.S)
            with self.subTest(task=t):
                self.assertIsNotNone(m)
                self.assertNotIn('id="task-data-asap7"', a7)
                data = json.loads(m.group(1))
                self.assertNotIn("points", data)            # the scoring point only
                self.assertNotIn("scaling", data)
                self.assertFalse({"energy_fj", "energy_cycle_fj", "leakage_nw"} & {x["key"] for x in data["metrics"]})
                area = next(x for x in data["metrics"] if x["key"] == "area_um2")
                self.assertIn("placed and routed", area["what"])
                stem, _ = self.a7_par(t)
                for d in data["designs"]:
                    e = self.bound(t, lb.sha256_file(self.design_file(t, d)))
                    if e is None:                           # no bound routed entry: no routed number at all
                        self.assertNotIn("adp", d["m"])
                        self.assertNotIn("area_um2", d["m"])
                        continue
                    vo = e["scores"]["v_owner"]
                    self.assertEqual(d["m"]["area_um2"], vo["area_e5um2"] / 100000)
                    self.assertEqual(d["m"]["time_ps"], vo["time_ps"])
                    self.assertEqual(d["m"]["adp"], vo["area_e5um2"] * vo["time_ps"] / 1e8)
                self.assertEqual([d["name"] for d in data["designs"] if d["par"]], [stem] if stem else [])
                score = section(view_of(a7, R), "score")
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

    def test_every_detail_page_shows_its_routed_result_or_why_not(self):
        """A record page on the routed course: with a bound entry, its routed area, time and score, the cells-only
        column and the run, and its reproduce block the run's files; without one, "not routed yet" and no routed number
        (never the cells-only or a stale number in its place)."""
        seen = {"bound": 0, "not": 0}
        for rec in self.records:
            t = rec["task"]
            if t not in self.listed:
                continue
            path = f"tasks/{t}/records/{rec['record_hash']}.html"
            e = self.bound(t, rec["files"]["sv"]["sha256"])
            a0 = lb.asap7_entry(lb.load_asap7(t), rec["files"]["sv"]["sha256"])
            dash = text_of(section(self.view(path, R), "dashboard"))
            rep = text_of(section(self.view(path, R), "reproduce"))
            with self.subTest(page=path):
                if e is None:
                    seen["not"] += 1
                    self.assertIn("No ranked numbers to show: not routed yet: place and route pending.", dash)
                    self.assertIn("No routed result for this design: not routed yet: place and route pending.", rep)
                    self.assertNotIn("µm² exactly", dash)
                    continue
                seen["bound"] += 1
                vo = e["scores"]["v_owner"]
                self.assertIn(flat(f"{build.grouped(lb.fmt_um2_e5(vo['area_e5um2']))} µm² exactly"), dash)
                self.assertIn(flat(f"{build.thin(vo['time_ps'])} ps"), dash)
                self.assertIn(flat(combined.fmt(combined.um2ns(vo["exact"], R))), dash)
                self.assertIn("cells only (A0′)", dash)
                self.assertIn(f"seed {vo['seed']}, valid", dash)
                wire = vo["exact"] / (a0["area_e5um2"] * a0["time_ps"]) - 1
                self.assertIn(("+" if wire > 0 else "−") + f"{abs(wire) * 100:.1f}%", dash)
                run = next(r for r in e["runs"] if r["role"] == "scoring")
                for h in (run["artifacts"]["6_final.v"], run["artifacts"]["6_final.odb"], run["config_mk_sha256"],
                          str(run["area_e5um2"])):
                    self.assertIn(h, rep)
                self.assertIn(self.pins["image"]["manifest_digest"], rep)
                sky = text_of(section(self.view(path, "sky130"), "dashboard"))
                self.assertNotIn(flat(f"{build.grouped(lb.fmt_um2_e5(vo['area_e5um2']))} µm² exactly"), sky)
        # every design is routed since 2026-11-13: a page without a bound entry is planted in
        # test_a_design_not_routed_yet_shows_no_routed_number
        self.assertTrue(seen["bound"], seen)

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
                    a7 = section(self.view(f"tasks/{t}/index.html", R), "references")
                    self.assertIn(flat(combined.fmt(combined.um2ns(exact, R))), text_of(a7))
                self.assertEqual(len(re.findall(r'class="[^"]*\bpar-a7\b', refs)), 1 if stem else 0)

    def test_the_machine_outputs_carry_both_views(self):
        summary = json.loads(self.files["data/site.json"])
        for x in summary["tasks"]:
            with self.subTest(task=x["name"]):
                self.assertEqual(x["ranked_axes"], ["area_um2_sky130", "time_ps"])
                self.assertNotIn("asap7", x)
                self.assertEqual(x[R]["ranked_axes"], ["area_um2_asap7pnr", "time_ps"])
                self.assertEqual(x[R]["results"], f"leaderboard/asap7pnr/{x['name']}.json")
                stem, _ = self.a7_par(x["name"])
                self.assertEqual((x[R]["par"] or {}).get("design"), stem)
                data = json.loads(self.files[f"data/tasks/{x['name']}.json"])
                sky, a7 = self.boards(x["name"])
                self.assertEqual([r["record_hash"] for r in data[R]["submissions_board"]["ranking"]],
                                 [r["record_hash"] for r in a7["ranking"]])
                self.assertEqual(sorted(x[R]["not_routed"]), sorted(r["record_hash"] for r in a7["unranked"]))
                self.assertEqual(data[R]["submissions_board"]["pdk"], R)
                self.assertEqual(data["submissions_board"]["pdk"], "sky130")

    def test_the_task_text_says_it_quotes_sky130_numbers_on_the_routed_course(self):
        """The task section's text (content/tasks/<t>.md) quotes sky130's area, time and score and compares designs by
        them; the routed course says so above it (a review finding, 2026-11-09), the sky130 view does not. GE and depth
        are the same on either library, so a text quoting only them needs no note."""
        note = "This text quotes sky130 numbers"
        for t in self.listed:
            with open(os.path.join(SITE, "content", "tasks", f"{t}.md"), encoding="utf-8") as fh:
                raw = fh.read()
            quotes = bool(re.search(r"\{\{\s*[A-Za-z0-9_]+\.(area|time|score)\s*\}\}", raw))
            with self.subTest(task=t):
                a7 = text_of(section(self.view(f"tasks/{t}/index.html", R), "statement"))
                sky = text_of(section(self.view(f"tasks/{t}/index.html", "sky130"), "statement"))
                self.assertEqual(note in a7, quotes)
                self.assertNotIn(note, sky)
        self.assertIn(note, text_of(section(self.view("tasks/add/index.html", R), "statement")))

    def test_par_sits_in_its_place_on_each_board_and_the_lead_beats_par(self):
        """The leaderboard list puts par's row under the records that beat par and above the rest, in both views; the
        first record is highlighted as the lead only when it beats par (on the routed add board since 2026-11-13: three
        records beat par, fernladder's Sklansky adder first, then par, then the rest, select-six last; on the routed
        _example board the one record ties par, so par comes first and there is no lead)."""
        for t in self.listed:
            sky, a7 = self.boards(t)
            task = self.task(t)
            sky_par = lb.par_of(task, [r for r in self.records if r["task"] == t], flow=pinned_flow(task),
                                identity=lb.ppa_identity(), input_drive=lb.ppa_setup_now(task).get("input_drive"),
                                statement=lb.current_statement_or_none(task),
                                names=lb.par_names(lb.DEFAULT_TASKS, task))
            pars = {"sky130": sky_par["exact"] if sky_par else None, R: self.a7_par(t)[1]}
            for pdk, board in (("sky130", sky), (R, a7)):
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
        lst = section(self.view("tasks/add/index.html", R), "leaderboard")
        ol = lst.split('<ol class="board">', 1)[1].split("</ol>", 1)[0]
        rows = re.findall(r'<li(?: class="(lead|par)")?>(.*?)</li>', ol, re.S)
        self.assertEqual([k for k, _ in rows], ["lead", "", "", "par", "", "", ""])
        self.assertIn("fernladder", text_of(rows[0][1]))
        self.assertIn("select-six", text_of(rows[-1][1]))
        lst = section(self.view("tasks/_example/index.html", R), "leaderboard")
        ol = lst.split('<ol class="board">', 1)[1].split("</ol>", 1)[0]
        rows = re.findall(r'<li(?: class="(lead|par)")?>(.*?)</li>', ol, re.S)
        self.assertEqual([k for k, _ in rows], ["par", ""])

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
                             (R, ((summary[t].get(R) or {}).get("par") or {}).get("design"))):
                head = text_of(self.view(path, pdk).split('id="dashboard"', 1)[0])
                with self.subTest(page=path, pdk=pdk):
                    if stem is not None and stem == par:
                        seen["par"] += 1
                        self.assertIn("It is par, the bar to beat", head)
                        self.assertIn("par, not an entry", head)
                        self.assertNotIn("par's design: not an entry", head)
                    else:
                        seen["not"] += 1
                        self.assertIn("It is shown with par", head)
                        self.assertNotIn("It is par", head)
                        self.assertIn("par's design: not an entry", head)
        self.assertTrue(seen["par"] and seen["not"], seen)

    def test_the_home_selector_may_shrink_on_a_phone(self):
        """The home page's course control sits in the course head's flex line; the rule that keeps the heading at its
        width must not keep it at its one-line width (2026-11-09: the front page scrolled sideways on a phone; since
        2026-11-11 the block is `.course-pick`)."""
        with open(os.path.join(SITE, "style.css"), encoding="utf-8") as fh:
            css = fh.read()
        rule = re.search(r"\.course > \.section-head > \.course-pick \{([^}]*)\}", css)
        self.assertIsNotNone(rule)
        self.assertIn("min-width: 0", rule.group(1))
        self.assertRegex(rule.group(1), r"flex: 1 1 auto")
        self.assertGreater(rule.start(), css.index(".course > .section-head > div {"))

    def test_the_header_label_leaves_the_line_on_a_small_phone(self):
        """The header's "Course" label is visually hidden, its name kept for a screen reader, on every width where it
        would wrap the header beside the course's name (2026-11-11: measured to 351 px, so under 22rem)."""
        with open(os.path.join(SITE, "style.css"), encoding="utf-8") as fh:
            css = fh.read()
        block = re.search(r"@media \(max-width: (\d+(?:\.\d+)?)rem\) \{\s*\.site-header \.pdk-pick label \{([^}]*)\}", css)
        self.assertIsNotNone(block)
        self.assertGreaterEqual(float(block.group(1)), 22)
        for prop in ("position: absolute", "width: 1px", "height: 1px", "overflow: hidden", "clip-path: inset(50%)"):
            self.assertIn(prop, block.group(2))
        self.assertNotIn("display: none", block.group(2))         # the select keeps its accessible name

    def test_a_design_without_a_bound_asap7_entry_is_a_build_warning(self):
        """`asap7_gaps`: a design the ASAP7 view would show without a bound entry, or a task without its file, is a
        warning of the build (fatal under --strict), so that a publish build never ships a partial view (a review
        finding, 2026-11-09). The committed files have none. (The ASAP7 view is the routed course's input since
        2026-11-12: its netlists are what the routed results bind to.)"""
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

    def test_a_design_not_routed_yet_is_a_note_and_a_bad_entry_a_warning(self):
        """`asap7pnr_gaps` (the routed course, 2026-11-12): a design not routed yet is a NOTE of the build, never a
        warning (the course is filled after the record, and the page says "not routed yet"); a stale, unbound or failed
        entry is a warning, fatal under --strict. The committed files: no warning (and no note: every design the tasks
        show is routed since 2026-11-13); a design not routed yet is planted on a copy of add's table."""
        self.assertFalse([w for w in self.site.warnings if "asap7pnr" in w], self.site.warnings)

        class Fake:
            def __init__(self):
                self.warnings, self.notes, self.pnr_identity = [], [], lb.asap7pnr_identity()

            def warn(self, msg):
                self.warnings.append(msg)

        with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
            expected = json.load(fh)
        t = build.Task("add", self.task("add"), "listed")
        t.records = [r for r in self.records if r["task"] == "add"]
        a7, pnr = lb.load_asap7("add"), lb.load_asap7pnr("add")
        fake = Fake()
        build.asap7pnr_gaps(fake, t, a7, pnr, expected)
        self.assertEqual(fake.warnings, [])
        live = list(fake.notes)
        # one design not routed yet (its entry gone from a copy): a note naming it, never a warning
        gone = pnr["designs"][0]
        fake = Fake()
        build.asap7pnr_gaps(fake, t, a7, dict(pnr, designs=pnr["designs"][1:]), expected)
        self.assertEqual(fake.warnings, [])
        self.assertEqual(sorted(set(fake.notes) - set(live)),
                         [f"add: routed course: {', '.join(gone['of'])}: not routed yet: place and route pending"])
        self.assertEqual(len(fake.notes), len(live) + 1)
        # the course pins changed: every entry is stale, a warning each
        stale = json.loads(json.dumps(pnr))
        stale["course"]["image"]["tag"] = "another"
        fake = Fake()
        build.asap7pnr_gaps(fake, t, a7, stale, expected)
        self.assertEqual(len(fake.warnings), len(pnr["designs"]), fake.warnings)
        self.assertTrue(all("stale: routed under another image, flow or settings" in w for w in fake.warnings))
        # an entry whose placed netlist is not its design's: unbound
        unbound = json.loads(json.dumps(pnr))
        unbound["designs"][0]["netlist_sha256"] = "0" * 64
        fake = Fake()
        build.asap7pnr_gaps(fake, t, a7, unbound, expected)
        self.assertEqual(len(fake.warnings), 1, fake.warnings)
        self.assertIn("unbound: its routed netlist is not this design's ASAP7 netlist", fake.warnings[0])

    def test_a_design_not_routed_yet_shows_no_routed_number(self):
        """A record not routed yet, end to end (planted: every design is routed since 2026-11-13). With fernladder's
        Sklansky adder's entry gone from add's routed file, the build notes it (no warning); on the routed course it
        is not on add's board but under "Not ranked" with "not routed yet: place and route pending" and dashes, its
        record page says why and shows "No layout yet" instead of a picture, its routed score is nowhere on add's
        pages, and the other tasks are untouched."""
        real = lb.load_asap7pnr
        recs = [r for r in self.records if r["task"] == "add"]
        skl = next(r for r in recs if r["record_hash"].startswith("f5ecef0e"))
        sha = skl["files"]["sv"]["sha256"]
        e = lb.asap7pnr_entry(real("add"), sha)
        self.assertIsNotNone(e)

        def drop_skl(task_name, *a, **kw):
            data = real(task_name, *a, **kw)
            if task_name == "add" and data is not None:
                data = dict(data, designs=[x for x in data["designs"] if x["sv_sha256"] != sha])
            return data
        try:
            lb.load_asap7pnr = drop_skl
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                site = build.build_site(offline=True)
        finally:
            lb.load_asap7pnr = real
        self.assertFalse([w for w in site.warnings if "asap7pnr" in w], site.warnings)
        self.assertTrue([n for n in site.notes if n.startswith("add: routed course:") and skl["record_hash"] in n
                         and "not routed yet: place and route pending" in n], site.notes)
        page = view_of(site.files["tasks/add/index.html"].decode("utf-8"), R)
        lst = section(page, "leaderboard")
        board, rest = lst.split('<ol class="board">', 1)[1].split("</ol>", 1)
        self.assertNotIn(skl["record_hash"], board)
        (tr,) = [x for x in re.findall(r"<tr>(.*?)</tr>", rest, re.S) if f"records/{skl['record_hash']}.html" in x]
        self.assertIn("not routed yet: place and route pending", text_of(tr))
        self.assertEqual(tr.count('<span class="muted">–</span>'), 2, tr)           # area and time
        self.assertNotIn(flat(combined.fmt(combined.um2ns(e["scores"]["v_owner"]["exact"], R))), text_of(page))
        path = f"tasks/add/records/{skl['record_hash']}.html"
        h = site.files[path].decode("utf-8")
        v = view_of(h, R)
        self.assertIn("No ranked numbers to show: not routed yet: place and route pending.",
                      text_of(section(v, "dashboard")))
        self.assertIn("No routed result for this design: not routed yet: place and route pending.",
                      text_of(section(v, "reproduce")))
        self.assertNotIn("µm² exactly", text_of(section(v, "dashboard")))
        figs = re.findall(r'<figure class="layout-fig[^"]*"[^>]*>(.*?)</figure>', section(h, "schematic"), re.S)
        self.assertEqual(len(figs), 1)
        self.assertIn("No layout yet: place and route pending.", text_of(figs[0]))
        self.assertNotIn("<img", figs[0])
        self.assertNotIn('class="layout-link"', h)
        self.assertFalse([p for p in site.files if p.startswith(f"tasks/add/layouts/{sha[:16]}")])
        self.assertEqual(site.files["tasks/mul/index.html"], self.files["tasks/mul/index.html"])

    def test_a_stale_routed_file_shows_no_routed_number(self):
        """The binding rule end to end (2026-11-12): with add's routed file made under other pins (its course block
        names another image), the site build warns, add's pages show NO routed number (par, record and under par are
        dashes, no record ranks, every record page says why, no layout picture), and the other tasks are untouched."""
        real = lb.load_asap7pnr

        def stale_add(task_name, *a, **kw):
            data = real(task_name, *a, **kw)
            if task_name == "add" and data is not None:
                data = json.loads(json.dumps(data))
                data["course"]["image"]["manifest_digest"] = "sha256:" + "0" * 64
            return data
        try:
            lb.load_asap7pnr = stale_add
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                site = build.build_site(offline=True)
        finally:
            lb.load_asap7pnr = real
        self.assertTrue([w for w in site.warnings if "add" in w and "stale" in w], site.warnings)
        page = view_of(site.files["tasks/add/index.html"].decode("utf-8"), R)
        head = text_of(section(page, "numbers"))
        self.assertEqual(head.count("–"), 3, head)
        stem, exact = self.a7_par("add")
        self.assertNotIn(flat(combined.fmt(combined.um2ns(exact, R))), text_of(page))
        lst = section(page, "leaderboard")
        self.assertEqual(re.findall(r'<a href="records/([0-9a-f]{64})\.html">',
                                    lst.split('<ol class="board">', 1)[1].split("</ol>", 1)[0]), [])
        for rec in [r for r in self.records if r["task"] == "add"]:
            path = f"tasks/add/records/{rec['record_hash']}.html"
            with self.subTest(page=path):
                h = site.files[path].decode("utf-8")
                why = ("stale: routed under another image, flow or settings"
                       if lb.asap7pnr_entry(real("add"), rec["files"]["sv"]["sha256"]) else
                       "not routed yet: place and route pending")
                self.assertIn(why, text_of(view_of(h, R)))
                self.assertNotIn('class="layout-link"', h)
        self.assertFalse([p for p in site.files if p.startswith("tasks/add/layouts/")])
        self.assertEqual(site.files["tasks/mul/index.html"], self.files["tasks/mul/index.html"])

    def test_a_routed_file_of_another_scoring_point_shows_no_routed_number(self):
        """The binding rule's scoring point, end to end (a review finding, 2026-11-13: the board rows took the routed
        numbers without the task, so a file stale by its scoring point alone still put them in the "Not ranked"
        table). With sorter's routed file made at another scoring point, the build warns, and no sorter page shows a
        routed number: par, record and under par are dashes, no record ranks, each record is under "Not ranked" with
        the reason and dashes for area and time, each record page says why."""
        real = lb.load_asap7pnr

        def stale_sorter(task_name, *a, **kw):
            data = real(task_name, *a, **kw)
            if task_name == "sorter" and data is not None:
                data = json.loads(json.dumps(data))
                data["scoring_point"]["N"] = 16
            return data
        try:
            lb.load_asap7pnr = stale_sorter
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                site = build.build_site(offline=True)
        finally:
            lb.load_asap7pnr = real
        why = "stale: routed at {'N': 16, 'W': 8}, the task's scoring point is {'N': 8, 'W': 8}"
        self.assertTrue([w for w in site.warnings if w.startswith("sorter:") and why in w], site.warnings)
        page = view_of(site.files["tasks/sorter/index.html"].decode("utf-8"), R)
        self.assertEqual(text_of(section(page, "numbers")).count("–"), 3)
        lst = section(page, "leaderboard")
        board, rest = lst.split('<ol class="board">', 1)[1].split("</ol>", 1)
        self.assertEqual(re.findall(r'<a href="records/([0-9a-f]{64})\.html">', board), [])
        shown = text_of(page)
        mine = [r for r in self.records if r["task"] == "sorter" and r["player"] != self.config["reference_player"]]
        self.assertTrue(mine)
        for rec in [r for r in self.records if r["task"] == "sorter"]:
            e = lb.asap7pnr_entry(real("sorter"), rec["files"]["sv"]["sha256"])
            vo = e["scores"]["v_owner"]
            with self.subTest(record=rec["record_hash"][:12]):
                self.assertNotIn(flat(combined.fmt(combined.um2ns(vo["exact"], R))), shown)
                self.assertNotIn(lb.fmt_um2_e5(vo["area_e5um2"]), shown)
                h = site.files[f"tasks/sorter/records/{rec['record_hash']}.html"].decode("utf-8")
                self.assertIn(why, text_of(view_of(h, R)))
                self.assertNotIn(flat(combined.fmt(combined.um2ns(vo["exact"], R))), text_of(view_of(h, R)))
                if rec in mine:
                    (tr,) = [x for x in re.findall(r"<tr>(.*?)</tr>", rest, re.S)
                             if f"records/{rec['record_hash']}.html" in x]
                    self.assertIn(why, html.unescape(tr))
                    self.assertEqual(tr.count('<span class="muted">–</span>'), 2, tr)       # area and time
        self.assertEqual(site.files["tasks/mul/index.html"], self.files["tasks/mul/index.html"])

    def test_the_sky130_view_is_the_page_without_the_selector(self):
        """The default view shows the sky130 numbers exactly where they were: the sky130 board's numbers and par's
        sky130 score are in it, and no routed score is."""
        for t in self.listed:
            sky, a7 = self.boards(t)
            page = text_of(self.view(f"tasks/{t}/index.html", "sky130"))
            with self.subTest(task=t):
                for r in sky["ranking"]:
                    self.assertIn(flat(combined.fmt(r["um2ns"])), page)
                self.assertNotIn("ASAP7 routed · area × time", page)
                self.assertNotIn("Score = area × time on ASAP7", page)


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
