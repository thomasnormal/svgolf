"""The site's pages of an exploration task (site/explorepage.py): an offline build, then what the pages say.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)

An exploration task has no statement: its entries are UNPROVED and its score is COMPOSED. The tests hold the site to
that: the task page and the home page's card say so, the board is not a leaderboard, and nothing of the task is among
the ranked tasks' data, the latest records or the machine-readable boards.
"""
import contextlib
import html
import importlib.util
import io
import json
import os
import re
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")


def load_build():
    sys.path.insert(0, SITE)
    spec = importlib.util.spec_from_file_location("svgolf_site_build_explore", os.path.join(SITE, "build.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


build = load_build()
xb = build.lbx


def text_of(page_html):
    """A page's visible text, whitespace squeezed."""
    body = re.sub(r"<(script|style)\b.*?</\1>", " ", page_html, flags=re.S)
    return " ".join(html.unescape(re.sub(r"<[^>]+>", " ", body)).split())


class ExplorePages(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        out = os.path.join(cls.tmp.name, "site")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            rc = build.main(["--offline", "--out", out])
        if rc != 0:
            raise AssertionError(f"build.py --offline exited {rc}")
        cls.out = out
        cls.config = build.load_config()
        cls.tasks = [t for t, how in cls.config["explore_tasks"].items() if how == "listed"]

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def read(self, rel, binary=False):
        with open(os.path.join(self.out, rel), "rb" if binary else "r", **({} if binary else {"encoding": "utf-8"})) as fh:
            return fh.read()

    def test_gemm_is_an_exploration_task_and_not_a_ranked_one(self):
        self.assertEqual(self.tasks, ["gemm"])
        self.assertNotIn("gemm", self.config["tasks"])
        self.assertEqual(xb.task_names(), ["gemm"])

    def test_the_task_page_says_unproved_and_composed(self):
        for t in self.tasks:
            page = self.read(f"explore/{t}/index.html")
            text = text_of(page)
            with self.subTest(task=t):
                self.assertIn("exploration: unproved entries", text)
                self.assertIn("Exploration board", text)
                self.assertIn("unproved · composed · lower is better", text)
                self.assertIn("Not a leaderboard: no entry here has a proof.", text)
                self.assertIn("no wires, no clock tree", text)
                self.assertIn("which a wrong design can pass too", text)
                self.assertIn("The cycles per job were measured by running the scored job with identity weights", text)
                # the limits and the first entries' standing are sections the page shows open, and the foot links them
                self.assertIn('href="#what-the-check-does-not-show"', page)
                self.assertRegex(page, r'<section id="what-the-check-does-not-show"><h3>')
                self.assertRegex(page, r'<section id="the-first-entries"><h3>')
                self.assertIn("No entry of this task is proved.", text)
                self.assertIn("As arithmetic on the board's figures, not a measurement", text)
                self.assertIn("none yet: every entry is unproved", text)
                self.assertIn("What a proof will have to show", text)
                # none of the ranked pages' words: no record, no leaderboard card, no under par, no course selector text
                for word in ("Leaderboard", "under par", "record holder", "How to submit", "kernel-checked proof of the "
                             "statement, recorded"):
                    self.assertNotIn(word, text)
                self.assertNotIn('id="leaderboard"', page)
                self.assertIn('id="board"', page)
                self.assertIn('id="scoring"', page)

    def test_the_board_lists_the_boards_entries_by_score_with_par_marked(self):
        for t in self.tasks:
            board = xb.load(t)
            page = self.read(f"explore/{t}/index.html")
            m = re.search(r'<section class="card[^"]*" id="board">(.*?)</section>', page, re.S)
            self.assertIsNotNone(m)
            rows = re.findall(r"<tr[^>]*>(.*?)</tr>", m.group(1), re.S)[1:]
            order = [e["name"] for e in xb.ordered(board)]
            self.assertEqual(len(rows), len(order))
            self.assertGreaterEqual(len(order), 1)
            for row, name in zip(rows, order):
                e = next(x for x in board["entries"] if x["name"] == name)
                cells = [text_of(c) for c in re.findall(r"<td[^>]*>(.*?)</td>", row, re.S)]
                with self.subTest(entry=name):
                    self.assertTrue(cells[0].startswith(name), cells[0])
                    self.assertEqual("par" in cells[0].split(), bool(e.get("par")))
                    self.assertEqual(cells[1], f"{xb.mm2ms(e):.2f}")
                    self.assertEqual(cells[3], f"{e['score']['area_um2'] / 1e6:.3f}")
                    self.assertEqual(int(re.sub(r"\D", "", cells[4])), e["score"]["cycles"])
                    self.assertEqual(e["score"]["cycles_measured"], e["score"]["cycles"])
                    self.assertEqual(int(re.sub(r"\D", "", cells[5])), e["score"]["period_ps"])
            par = xb.par_entry(board)
            self.assertIsNotNone(par)
            par_row = next(r for r, n in zip(rows, order) if n == par["name"])
            self.assertEqual(text_of(re.findall(r"<td[^>]*>(.*?)</td>", par_row, re.S)[2]), "1.000")

    def test_the_entries_files_are_offered_byte_for_byte(self):
        for t in self.tasks:
            for e in xb.load(t)["entries"]:
                for key, ext in (("sv", ".sv"), ("declare", ".json")):
                    with open(os.path.join(SVGOLF, e[key]), "rb") as fh:
                        self.assertEqual(self.read(f"explore/{t}/entries/{e['name']}{ext}", binary=True), fh.read())
            for rel in ("task.json", "oracle.py", "env/tb.sv"):
                with open(os.path.join(SVGOLF, "tasks", t, rel), "rb") as fh:
                    self.assertEqual(self.read(f"explore/{t}/{rel}", binary=True), fh.read())

    def test_a_players_entry_shows_its_player_and_its_writeup_on_a_page_of_its_own(self):
        for t in self.tasks:
            board = xb.load(t)
            index = self.read(f"explore/{t}/index.html")
            for e in board["entries"]:
                path = os.path.join(self.out, "explore", t, "entries", f"{e['name']}.html")
                with self.subTest(entry=e["name"]):
                    if "player" not in e:
                        self.assertFalse(os.path.exists(path))         # the maintainers' entries: no page, no player
                        continue
                    self.assertIn(f'href="entries/{e["name"]}.html"', index)
                    self.assertIn(f"by {e['player']}", text_of(index))
                    page = self.read(f"explore/{t}/entries/{e['name']}.html")
                    text = text_of(page)
                    with open(xb.writeup_path(t, e["name"]), encoding="utf-8") as fh:
                        title = build.lb.writeup_title(fh.read())
                    self.assertIn(title, text)
                    self.assertIn('class="writeup-body"', page)
                    self.assertIn("exploration: unproved entries", text)
                    self.assertIn(f"player {e['player']}", text)
                    self.assertIn("assisted by " + "; ".join(e["assisted_by"]), text)
                    self.assertIn(f"{xb.mm2ms(e):.2f}", text)
                    self.assertIn("none: the entry is unproved", text)
                    self.assertIn(f'href="{e["name"]}.sv"', page)

    def test_the_home_page_lists_it_in_a_block_of_its_own(self):
        home = self.read("index.html")
        ranked = re.findall(r'<li class="task-card">(.*?)</li>', home, re.S)
        cards = re.findall(r'<li class="task-card explore-card">(.*?)</li>', home, re.S)
        self.assertEqual(len(cards), len(self.tasks))
        block = home[home.index('id="exploration"'):]
        self.assertLess(home.index('<ul class="task-cards">'), home.index('id="exploration"'))    # under the ranked cards
        self.assertIn("nothing here is proved", text_of(block[:block.index("</ul>")]))
        for t in self.tasks:
            self.assertFalse(any(f"/{t}/index.html" in c for c in ranked))                   # not among the ranked cards
            mine = [c for c in cards if f'href="explore/{t}/index.html"' in c]
            self.assertEqual(len(mine), 1)
            text = text_of(mine[0])
            self.assertIn("exploration", text)
            self.assertIn("exploration: unproved entries", text)
            self.assertIn("Plain design", text)
            self.assertIn("Best entry", text)
            self.assertIn("Unproved", text)
            for word in ("Par", "Record", "Under par"):                  # the ranked cards' three, never here
                self.assertNotIn(f">{word}<", mine[0])

    def test_nothing_of_it_is_in_the_ranked_data_or_the_latest_records(self):
        summary = json.loads(self.read("data/site.json"))
        self.assertNotIn("gemm", [x["name"] for x in summary["tasks"]])
        self.assertFalse(os.path.exists(os.path.join(self.out, "data", "tasks", "gemm.json")))
        self.assertNotIn("gemm", self.read("latest.html"))
        self.assertFalse(os.path.exists(os.path.join(self.out, "tasks", "gemm")))           # no page among the tasks' pages

    def test_a_board_whose_file_changed_fails_the_build(self):
        site = build.Site(build.load_config())
        import explorepage
        real = xb.problems
        try:
            xb.problems = lambda name: [f"{name}: entry par: x.sv is not the file the entry was checked on"]
            with self.assertRaises(build.BuildError) as cm:
                explorepage.collect(site, xb, ["gemm"], os.path.join(SVGOLF, "tasks"), {"gemm": "listed"},
                                    build.BuildError)
            self.assertIn("exploration board", str(cm.exception))
        finally:
            xb.problems = real


if __name__ == "__main__":
    unittest.main()
