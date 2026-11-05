"""The svGolf site as a whole: built once with --offline into a temporary
directory, then checked file by file against the repository.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)

No network, no Yosys, no Lean. The checks are written independently of the
generator's own guards (site/build.py runs a link check and the denylist
scan itself; these tests do not reuse that code).
"""

import contextlib
import hashlib
import html
import html.parser
import importlib.util
import io
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
BUILD_PY = os.path.join(SITE, "build.py")


def load_build():
    """site/build.py under a private name (a module called `build` may be installed)."""
    sys.path.insert(0, SITE)
    spec = importlib.util.spec_from_file_location("svgolf_site_build", BUILD_PY)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


build = load_build()
lb = build.lb


def read_tree(top):
    out = {}
    for d, dirs, files in os.walk(top):
        dirs.sort()
        for f in sorted(files):
            p = os.path.join(d, f)
            with open(p, "rb") as fh:
                out[os.path.relpath(p, top).replace(os.sep, "/")] = fh.read()
    return out


class Page(html.parser.HTMLParser):
    """The ids, links, tags and `<pre data-src>` texts of one page."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.tags, self.marks = set(), [], [], []
        self.src_blocks, self._pre, self._buf = [], None, []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        self.tags.append((tag, a))
        if a.get("id"):
            self.ids.add(a["id"])
        for k in ("href", "src"):
            if a.get(k) is not None:
                self.links.append((tag, k, a[k]))
        if tag == "pre" and "data-src" in a:
            self._pre, self._buf = a["data-src"], []
        if tag == "g" and "data-kind" in a:
            self.marks.append(a)

    def handle_endtag(self, tag):
        if tag == "pre" and self._pre is not None:
            self.src_blocks.append((self._pre, "".join(self._buf)))
            self._pre = None

    def handle_data(self, data):
        if self._pre is not None:
            self._buf.append(data)


def parse(data):
    p = Page()
    p.feed(data.decode("utf-8"))
    p.close()
    return p


def pinned_flow():
    with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
        pin = json.load(fh)["flow"]
    return {"yosys": pin["yosys_version"], "canon_script_sha256": pin["canon_script_sha256"],
            "script_sha256": pin["script_sha256"], "ge_table_sha256": pin["ge_table_sha256"]}


def records():
    return lb.good_records(lb.load_records(os.path.join(SVGOLF, "leaderboard", "data")))


def text_of(data):
    """A page's text: tags dropped, entities decoded."""
    s = data.decode("utf-8") if isinstance(data, bytes) else data
    return html.unescape(re.sub(r"<[^>]+>", "", s))


def norm(s):
    """Text compared loosely: Markdown code marks dropped, whitespace collapsed."""
    return " ".join(s.replace("`", "").split())


def sky130_scores(task_name):
    """{design file sha256: exact area x time (1e-4 um^2 x ps)} of the task's designs at its scoring
    point, read here from the sources the site must use (the sky130 goldens of score/tests/ppa/ for
    a combinational design, else a reference's own record, tests/expected.json's clocked columns),
    independently of the generator."""
    task = lb.load_task(os.path.join(SVGOLF, "tasks"), task_name)
    point = lb.scoring_point(task)
    out = {}
    with open(os.path.join(SVGOLF, "score", "tests", "ppa", "designs.json"), encoding="utf-8") as fh:
        designs = json.load(fh)["designs"]
    with open(os.path.join(SVGOLF, "score", "tests", "ppa", "expected_ppa.json"), encoding="utf-8") as fh:
        gold = json.load(fh)["designs"]
    for d in designs:
        if d["task"] == task_name and (d.get("params") or {}) == point and d["name"] in gold:
            with open(os.path.join(SVGOLF, d["src"]), "rb") as fh:
                out[hashlib.sha256(fh.read()).hexdigest()] = gold[d["name"]]["area_e4um2"] * gold[d["name"]]["delay_ps"]
    # a reference with no golden: its own record's sky130 columns, when comparable (the current pins and the task's drive)
    ident, drive = lb.ppa_identity(), lb.ppa_setup_now(task).get("input_drive")
    for r in records():
        p = r.get("ppa") or {}
        if (r["task"] == task_name and r["player"] == "svgolf-reference" and p.get("available") is True
                and r["files"]["sv"]["sha256"] not in out and r["score"]["scoring_point"] == point
                and all(p.get(k) == ident.get(k) for k in lb.PPA_IDENTITY) and lb.ppa_input_drive(p) == drive):
            out[r["files"]["sv"]["sha256"]] = p["area_e4um2_sky130"] * p["delay_ps_sky130"]
    with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
        exp = json.load(fh)["tasks"].get(task_name, {})
    key = ",".join(f"{k}={v}" for k, v in point.items()) or "default"
    for ref in task.get("references", []):
        s = ((exp.get("references", {}).get(posixpath.splitext(posixpath.basename(ref["sv"]))[0]) or {})
             .get("scores") or {}).get(key) or {}
        if "time_ps" in s:
            with open(os.path.join(SVGOLF, "tasks", task_name, ref["sv"]), "rb") as fh:
                out[hashlib.sha256(fh.read()).hexdigest()] = round(s["area_um2"] * 10000) * s["time_ps"]
    return out


def par_score(task_name):
    """The exact score of the task's best proved reference, or None when none is weighed."""
    task = lb.load_task(os.path.join(SVGOLF, "tasks"), task_name)
    scores = sky130_scores(task_name)
    mine = []
    for ref in task.get("references", []):
        with open(os.path.join(SVGOLF, "tasks", task_name, ref["sv"]), "rb") as fh:
            sha = hashlib.sha256(fh.read()).hexdigest()
        if sha in scores:
            mine.append(scores[sha])
    return min(mine) if mine else None


def section(page_html, sid):
    """The HTML of a task page's `<section id=sid>` (other attributes, a card's class, allowed)."""
    m = re.search(rf'<section\b[^>]*\bid="{re.escape(sid)}"[^>]*>', page_html)
    if not m:
        raise AssertionError(f"no <section id={sid!r}>")
    return page_html[m.end():].split("</section>", 1)[0]


class SiteTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.out = os.path.join(cls.tmp.name, "site")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            rc = build.main(["--offline", "--out", cls.out])
        if rc != 0:
            raise AssertionError(f"build.py --offline exited {rc}")
        cls.files = read_tree(cls.out)
        cls.pages = {p: parse(d) for p, d in cls.files.items() if p.endswith(".html")}
        cls.config = build.load_config()
        cls.listed = [t for t, how in cls.config["tasks"].items() if how != "hidden"]
        cls.previews = [t for t, how in cls.config["tasks"].items() if how == "preview"]
        cls.ranked = [t for t in cls.listed if t not in cls.previews]

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_every_listed_task_has_a_page_linked_from_home(self):
        home = {v for _, k, v in self.pages["index.html"].links if k == "href"}
        for t in self.listed:
            with self.subTest(task=t):
                self.assertIn(f"tasks/{t}/index.html", self.files)
                self.assertIn(f"tasks/{t}/index.html", home)
        for t, how in self.config["tasks"].items():
            if how == "hidden":
                self.assertNotIn(f"tasks/{t}/index.html", self.files)

    def test_relative_links_and_anchors_resolve(self):
        bad = []
        for path, p in sorted(self.pages.items()):
            for tag, attr, ref in p.links:
                if re.match(r"^[a-z][a-z0-9+.-]*:", ref):
                    continue                      # https:, mailto: (external, and only in <a>: below)
                self.assertFalse(ref.startswith("/"), f"{path}: absolute link {ref}")
                target, _, frag = ref.partition("#")
                dest = posixpath.normpath(posixpath.join(posixpath.dirname(path), target)) if target else path
                if dest not in self.files:
                    bad.append(f"{path}: {ref} -> missing {dest}")
                elif frag and frag not in self.pages.get(dest, Page()).ids:
                    bad.append(f"{path}: {ref} -> no #{frag} in {dest}")
        self.assertEqual(bad, [])

    def test_no_inline_or_external_script_and_no_external_css(self):
        """Scripts are the site's own files (`src` a relative path, no inline code); the one inline
        `<script>` allowed is inert data (`type="application/json"`). No event handler attributes."""
        for path, p in self.pages.items():
            with self.subTest(page=path):
                for tag, a in p.tags:
                    if tag != "script":
                        continue
                    if a.get("type") == "application/json":
                        self.assertNotIn("src", a)
                        continue
                    self.assertIn("src", a, f"{path}: an inline script")
                    self.assertIsNone(re.match(r"^[a-z][a-z0-9+.-]*:", a["src"]), f"{path}: script {a['src']}")
                for body in re.findall(r"<script\b([^>]*)>(.*?)</script>", self.files[path].decode("utf-8"), re.S):
                    if 'type="application/json"' not in body[0]:
                        self.assertEqual(body[1].strip(), "", f"{path}: inline script code")
                for tag, attr, ref in p.links:
                    if tag != "a":                # stylesheets, scripts, images, frames: local only
                        self.assertFalse(re.match(r"^[a-z][a-z0-9+.-]*:", ref) and not ref.startswith("data:"),
                                         f"{tag} {attr}={ref}")
                for tag, a in p.tags:
                    self.assertFalse(tag in ("iframe", "object", "embed"), tag)
                    self.assertFalse(any(k.startswith("on") for k in a), f"event handler on <{tag}>")
        css = self.files["style.css"].decode("utf-8")
        self.assertNotIn("@import", css)
        self.assertIsNone(re.search(r"url\(\s*['\"]?[a-z]+:", css))

    def test_spec_and_every_data_src_block_is_the_file_verbatim(self):
        seen = set()
        for path, p in self.pages.items():
            for src, text in p.src_blocks:
                with self.subTest(page=path, src=src):
                    with open(build.repo_file(src), "rb") as fh:
                        self.assertEqual(text.encode("utf-8"), fh.read())
                    seen.add((path, src))
        for t in self.listed:
            self.assertIn((f"tasks/{t}/index.html", f"svgolf/tasks/{t}/Spec.lean"), seen)

    def test_downloads_match_the_records(self):
        recs = [r for r in records() if r["task"] in self.listed]
        self.assertTrue(recs, "the repository has records")
        for rec in recs:
            h = rec["record_hash"]
            base = f"tasks/{rec['task']}/records/{h}"
            with self.subTest(record=h[:12]):
                self.assertEqual(hashlib.sha256(self.files[base + ".sv"]).hexdigest(), rec["files"]["sv"]["sha256"])
                self.assertEqual(hashlib.sha256(self.files[base + ".lean"]).hexdigest(), rec["files"]["lean"]["sha256"])
                self.assertEqual(lb.compute_record_hash(json.loads(self.files[base + ".json"])), h)
                self.assertIn(base + ".html", self.files)

    def test_reference_and_spec_downloads_are_the_repository_files(self):
        for t in self.listed:
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            pairs = [(f"tasks/{t}/Spec.lean", f"tasks/{t}/Spec.lean")]
            for ref in task.get("references", []):
                stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                pairs += [(f"tasks/{t}/reference/{stem}.sv", f"tasks/{t}/{ref['sv']}"),
                          (f"tasks/{t}/reference/{stem}.lean", f"tasks/{t}/{ref['lean']}")]
            for out, src in pairs:
                with self.subTest(file=out), open(os.path.join(SVGOLF, src), "rb") as fh:
                    self.assertEqual(self.files[out], fh.read())

    def test_chart_frontier_is_the_players_board_and_pareto(self):
        """The chart's record marks are the players' records; the reference player's records are par
        (drawn as the proved references), never ranked among them."""
        recs, flow, ref_player = records(), pinned_flow(), self.config["reference_player"]
        for t in self.listed:
            with self.subTest(task=t):
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                mine = [r for r in recs if r["task"] == t and r["player"] != ref_player]
                board = lb.build_board(task, mine, flow=flow, identity=lb.ppa_identity(),
                                       input_drive=lb.ppa_setup_now(task).get("input_drive"))
                marks = [m for m in self.pages[f"tasks/{t}/index.html"].marks if m["data-kind"] == "record"]
                on = {m["data-hash"] for m in marks if m["data-frontier"] == "true"}
                self.assertEqual(on, {r["record_hash"] for r in board["frontier"]})
                ranked = {r["record_hash"] for r in board["frontier"] + board["dominated"]}
                self.assertEqual(on, {r["record_hash"] for r in lb.pareto(
                    [lb.row_of(r) for r in mine if r["record_hash"] in ranked])})
                by_hash = {r["record_hash"]: r for r in mine}
                for m in marks:
                    self.assertIn(m["data-hash"], by_hash)
                    self.assertEqual(int(m["data-area-mge"]), by_hash[m["data-hash"]]["score"]["area_mge"])
                    self.assertEqual(int(m["data-depth"]), by_hash[m["data-hash"]]["score"]["depth"])

    def test_reference_records_are_par_not_players(self):
        ref_player = self.config["reference_player"]
        recs = records()
        self.assertTrue(any(r["player"] == ref_player for r in recs), "the repository has reference records")
        home = text_of(self.files["index.html"])
        self.assertNotIn(ref_player, home)
        self.assertNotIn("±0.0%", home)
        self.assertNotIn("solvers", home.lower())
        self.assertIn("open for submissions", home)
        self.assertNotIn("OPEN", home)
        for t in self.ranked:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                players = {r["player"] for r in recs if r["task"] == t and r["player"] != ref_player}
                tiles = text_of(section(html_, "numbers"))
                for big in ("Par", "Record", "Under par"):
                    self.assertIn(big, tiles)
                board = section(html_, "leaderboard")
                self.assertNotIn(ref_player, text_of(board))
                if not players and par_score(t) is not None:
                    self.assertIn("Under par0%", tiles)       # the references are the first entries
                elif not players:
                    self.assertIn("Par–", tiles)              # no sky130 weighing yet: no score
                if not players:
                    self.assertNotIn("vs par", tiles)
                    self.assertNotIn("against par", tiles)
                    self.assertIn("No submissions yet.", text_of(board))
                    self.assertNotIn("<table", board)
        for r in recs:
            if r["player"] == ref_player:
                page_ = text_of(self.files[f"tasks/{r['task']}/records/{r['record_hash']}.html"])
                self.assertIn("par, not an entry", page_)
                self.assertNotIn("on the Pareto frontier", page_)

    def test_par_is_the_best_proved_references_area_time(self):
        """PAR is area x time of the best weighed proved reference (computed here from the goldens),
        in the display unit; with no submissions RECORD is par. A task with no weighed reference has
        no score, and its score card says so instead of drawing."""
        c = build.combined
        weighed = 0
        for t in self.ranked:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                tiles = text_of(section(html_, "numbers"))
                par = par_score(t)
                if par is None:
                    self.assertIn("No design of this task has a sky130 weighing yet", text_of(section(html_, "score")))
                    continue
                weighed += 1
                self.assertIn("Par" + c.fmt(c.um2ns(par)) + c.UNIT, tiles)
                self.assertIn("Record" + c.fmt(c.um2ns(par)) + c.UNIT, tiles)
                data = json.loads(self.files["data/site.json"])
                summary = next(x for x in data["tasks"] if x["name"] == t)
                self.assertAlmostEqual(summary["score"]["par"], c.um2ns(par))
        self.assertGreaterEqual(weighed, 4)

    def test_previews_are_listed_and_not_ranked(self):
        """A preview (config.json `preview`) is listed on the home page and has its page, with its
        status line where a ranked task has its numbers and its leaderboard: no par, no record, no
        board, never "open for submissions"; the data says `ranked: false` and carries no board."""
        self.assertTrue(self.previews, "config.json lists previews")
        home_html = self.files["index.html"].decode("utf-8")
        summary = {x["name"]: x for x in json.loads(self.files["data/site.json"])["tasks"]}
        llms = self.files["llms.txt"].decode("utf-8")
        for t in self.previews:
            with self.subTest(task=t):
                with open(os.path.join(SVGOLF, "site", "content", "tasks", f"{t}.json"), encoding="utf-8") as fh:
                    note = json.load(fh)["preview_note"]
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                tiles = text_of(section(html_, "numbers"))
                self.assertIn(note, tiles)
                for big in ("Par", "Record", "Under par"):
                    self.assertNotIn(big, tiles)
                board = section(html_, "leaderboard")
                self.assertIn(note, text_of(board))
                self.assertNotIn("badge-par", board)
                self.assertNotIn("<table", board)
                self.assertNotIn("badge-par", section(html_, "references"))
                head = html_.split('<section id="numbers">', 1)[0]
                self.assertIn("preview: not ranked", head)
                self.assertNotIn("open for submissions", head)
                card = home_html.split(f'href="tasks/{t}/index.html"', 1)[1].split("</li>", 1)[0]
                self.assertIn("preview: not ranked", card)
                self.assertIn(note, text_of(card))
                self.assertNotIn("Par", text_of(card))
                s = summary[t]
                self.assertEqual((s["listing"], s["ranked"], s["par"], s["preview_note"]), ("preview", False, None, note))
                data = json.loads(self.files[f"data/tasks/{t}.json"])
                self.assertEqual((data["ranked"], data["board"], data["submissions_board"]), (False, None, None))
                self.assertFalse(any(r["par"] for r in data["references"]))
                self.assertIn(f"(`{t}`)", llms)
                self.assertIn("a preview, not ranked", llms.split(f"(`{t}`)", 1)[1].split("\n", 1)[0])
        for t in self.ranked:
            self.assertTrue(summary[t]["ranked"], t)

    def test_the_sky130_score_ranks_everywhere(self):
        """Decided 11/03: sky130 A0' ranks (area um^2, time ps); GE and depth are extra columns. The tables carry the
        sky130 pair before the GE pair, no page calls the sky130 columns unranked, and "Reproduce a score" is a page,
        generated from score/PPA.md's section of that name, linked from the rules, the home page and every task."""
        rp = self.files["reproduce.html"].decode("utf-8")
        with open(os.path.join(SVGOLF, "score", "PPA.md"), encoding="utf-8") as fh:
            ppa_md = fh.read()
        self.assertIn("## Reproduce a score", ppa_md)
        for phrase in ("Tools and pinned files", "The pinned flow, step by step", "Reproduce a recorded number",
                       "score/ppa.py --fetch-liberty", "ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5"):
            self.assertIn(phrase, ppa_md)
            self.assertIn(phrase, text_of(rp))
        self.assertNotRegex(rp, r"<h2[^>]*>The liberty")          # that section only, not the rest of PPA.md
        for src in ("rules.html", "index.html", "about.html", "roadmap.html", "llms.txt"):
            with self.subTest(page=src):
                self.assertIn("reproduce.html", self.files[src].decode("utf-8"))
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertIn("reproduce.html", section(html_, "score"))
                for sid in ("references", "baselines"):
                    head = section(html_, sid).split("</thead>", 1)[0]
                    if "<thead" not in head:
                        continue
                    heads_ = [text_of(h) for h in re.findall(r"<th\b[^>]*>(.*?)</th>", head, re.S)]
                    self.assertLess(heads_.index("area (µm²)"), heads_.index("GE · depth"), sid)
                    self.assertIn("time (ps)", heads_, sid)
        site_text = " ".join(text_of(self.files[p]) for p in ("index.html", "roadmap.html", "about.html", "rules.html"))
        for stale in ("(unranked)", "never rank anything", "(area, depth) Pareto", "the board is unchanged"):
            self.assertNotIn(stale, site_text)
        self.assertNotIn("(area, depth) Pareto", self.files["llms.txt"].decode("utf-8"))
        summary = json.loads(self.files["data/site.json"])
        for x in summary["tasks"]:
            self.assertEqual(x["ranked_axes"], ["area_um2_sky130", "time_ps"])

    def test_score_chart_and_explorer(self):
        """The score chart draws the proved references (dated) and the players' records, par as a
        line, and every weighed baseline as a level marked not proved, on a linear and a log axis.
        The explorer's data names every scored design with the pinned flow's numbers."""
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)["tasks"]
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                key = ",".join(f"{k}={v}" for k, v in lb.scoring_point(task).items()) or "default"
                m = re.search(r'<script type="application/json" id="task-data">(.*?)</script>', html_, re.S)
                data = json.loads(m.group(1))
                exp = expected.get(t, {})
                for d in data["designs"]:
                    if d["kind"] in ("reference", "baseline"):
                        s = exp[d["kind"] + "s"][d["name"]]["scores"][key]
                        self.assertEqual(round(d["m"]["area_ge"] * 1000), s["area_mge"], d["name"])
                        self.assertEqual(d["m"]["depth"], s["depth"], d["name"])
                refs = {posixpath.splitext(posixpath.basename(r["sv"]))[0] for r in task.get("references", [])
                        if (exp.get("references", {}).get(posixpath.splitext(posixpath.basename(r["sv"]))[0], {})
                            .get("scores") or {}).get(key)}
                self.assertEqual({d["name"] for d in data["designs"] if d["kind"] == "reference"}, refs)
                self.assertEqual(sum(1 for d in data["designs"] if d["par"]), 1 if refs and t in self.ranked else 0)
                score = section(html_, "score")
                if par_score(t) is None or t in self.previews:              # a preview draws no history
                    self.assertNotIn("<svg", score)
                    continue
                self.assertEqual(score.count('data-scale="linear"'), 2)          # wide and compact
                self.assertEqual(score.count('data-scale="log"'), 2)
                self.assertEqual(len(re.findall(r'data-scale="log"[^>]*\bhidden\b', score)), 2)
                wide = score.split('data-size="wide"', 1)[1].split("</svg>", 1)[0]
                self.assertIn('class="par-line"', wide)
                kinds = set(re.findall(r'<g class="mark[^"]*" data-kind="([a-z]+)"', wide))
                self.assertLessEqual(kinds, {"reference", "record"})
                weighed = [d for d in data["designs"] if d["kind"] == "baseline" and "adp" in d["m"]]
                self.assertEqual(wide.count('<line class="level"'), len(weighed))
                for d in weighed:
                    self.assertIn(f">{html.escape(d['name'])}</text>", wide)
                self.assertEqual(wide.count("not proved</text>") + wide.count("banned op</text>"), len(weighed))

    def test_charts_read_without_javascript(self):
        """The server draws every chart: the explorer's controls and the score chart's switch are
        hidden until charts.js shows them, the linear drawing is shown, and charts.js is a file of
        the site loaded by the task pages only."""
        self.assertIn("charts.js", self.files)
        for path, p in self.pages.items():
            srcs = [a.get("src", "") for tag, a in p.tags if tag == "script" and a.get("src")]
            uses = any(s.endswith("charts.js") for s in srcs)
            self.assertEqual(uses, path.startswith("tasks/") and path.endswith("/index.html"), path)
        for t in self.listed:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
                self.assertRegex(html_, r'<div class="explorer-controls" data-explorer-controls hidden>')
                self.assertIn("<svg", section(html_, "explore"))
                self.assertNotRegex(html_, r'data-scale="linear"[^>]*\bhidden\b')
                if "data-scale-toggle" in html_:
                    self.assertRegex(html_, r'data-scale-toggle hidden')

    # ---- measured at several points (score/measured/<task>.json, score/points.py)

    @staticmethod
    def measured(t):
        path = os.path.join(SVGOLF, "score", "measured", f"{t}.json")
        if not os.path.isfile(path):
            return None
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)

    def page_data(self, t):
        html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
        m = re.search(r'<script type="application/json" id="task-data">(.*?)</script>', html_, re.S)
        return html_, json.loads(m.group(1))

    def several(self):
        out = [t for t in self.listed if self.measured(t) and len(self.measured(t)["points"]) > 1]
        self.assertGreaterEqual(len(out), 4, out)        # add, mul, clmul, fdivp
        return out

    def test_the_explorer_offers_every_measured_point(self):
        """A task measured at several points: the page data names them in the order of the scaling parameter, the
        scored one (task.json's scoring point) marked, its button pressed and labelled as the ranked one; every other
        point's designs carry the measured numbers, read here from the data file independently of the generator
        (area in 1e-4 um^2, time, area x time, GE, depth), each marked measured and none par. The scored point's
        designs stay the ranked ones. A task of one point (aes_sbox) has no selector and no scaling view."""
        for t in self.listed:
            with self.subTest(task=t):
                html_, data = self.page_data(t)
                m = self.measured(t)
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                key = ",".join(f"{k}={v}" for k, v in lb.scoring_point(task).items()) or "default"
                if not m or len(m["points"]) < 2:
                    self.assertNotIn("points", data)
                    self.assertNotIn("data-point=", html_)
                    self.assertNotIn('id="scaling"', html_)
                    continue
                keys = [p["key"] for p in m["points"]]
                self.assertEqual([p["key"] for p in data["points"]], keys)
                self.assertEqual([p["key"] for p in data["points"] if p["scored"]], [key])
                ex = section(html_, "explore")
                self.assertIn('<div class="explorer-controls" data-explorer-controls hidden><div class="point-control">',
                              ex)
                buttons = re.findall(r'<button type="button" data-point="([^"]+)" aria-pressed="(true|false)"[^>]*>'
                                     r"([^<]*)</button>", ex)
                self.assertEqual([html.unescape(b[0]) for b in buttons], keys)
                mark = "· scored" if t in self.previews else "· ranked"       # a preview ranks nothing
                self.assertEqual([(html.unescape(b[0]), b[2].endswith(mark)) for b in buttons if b[1] == "true"],
                                 [(key, True)])
                self.assertEqual(sum(b[2].endswith(mark) for b in buttons), 1)
                self.assertEqual(sum("ranked" in b[2] for b in buttons), 0 if t in self.previews else 1)
                self.assertEqual(data.get("preview", False), t in self.previews)
                self.assertFalse(any(d.get("measured") for d in data["designs"]))
                self.assertNotIn(key, data["at"])
                for p in m["points"]:
                    if p["scored"]:
                        continue
                    got = {d["id"]: d for d in data["at"][p["key"]]}
                    want = {e["id"]: e["at"][p["key"]] for e in m["designs"] if p["key"] in e["at"]}
                    self.assertEqual(set(got), set(want), p["key"])
                    for i, row in want.items():
                        d = got[i]
                        self.assertTrue(d["measured"])
                        self.assertFalse(d["par"])
                        self.assertEqual(d["m"]["area_um2"], row["area_e4um2"] / 10000)
                        self.assertEqual(d["m"]["time_ps"], row["time_ps"])
                        self.assertEqual(d["m"]["adp"], row["area_e4um2"] * row["time_ps"] / 10_000_000)
                        self.assertEqual(round(d["m"]["area_ge"] * 1000), row["area_mge"])
                        self.assertEqual(d["m"]["depth"], row["depth"])

    def test_every_measured_point_reads_without_javascript(self):
        """Without JavaScript: the point note says what is drawn (the scored point: the ranked numbers) and that the
        other points are measured, not ranked; each other point has its own table of every design with all its
        numbers, under a heading that says measured, not ranked; and the scaling view is drawn by the server (wide
        and compact) for its first metric, one line per design with two points or more, its controls hidden until
        charts.js shows them, with a table of every line at every point, the scored column marked ranked. A preview
        (nothing of it ranked, no par) says so instead, and its scaling view draws the numbers themselves."""
        for t in self.several():
            with self.subTest(task=t):
                preview = t in self.previews
                html_, data = self.page_data(t)
                m = self.measured(t)
                ex = section(html_, "explore")
                names = {p["key"]: p["full"] for p in data["points"]}
                scored = next(p for p in data["points"] if p["scored"])
                note = re.search(r'<p class="point-note[^"]*" data-point-note>(.*?)</p>', ex, re.S)
                self.assertIsNotNone(note)
                note_text = norm(text_of(note.group(1)))
                what = "a preview, so nothing of it is ranked yet" if preview else "the ranked numbers"
                self.assertTrue(note_text.startswith(f"{scored['full']}, the scored point: {what}"), note_text)
                self.assertIn("measured, not ranked", note_text)
                text = norm(text_of(ex))
                for p in m["points"]:
                    if p["scored"]:
                        continue
                    summary = f"at {names[p['key']]} (measured, not ranked): every design with all its numbers"
                    self.assertIn(summary, text)
                    table = ex.split(html.escape(summary), 1)[1].split("</details>", 1)[0]
                    for e in m["designs"]:
                        if p["key"] in e["at"]:
                            area = e["at"][p["key"]]["area_e4um2"] / 10000
                            s = f"{area:.1f}"
                            if area >= 10000:
                                whole, frac = s.split(".")
                                s = f"{int(whole):,}".replace(",", "\u202f") + "." + frac
                            self.assertIn(f">{s}<", table, (t, e["id"], p["key"]))
                self.assertIn('<div class="explorer-controls" data-scaling-controls hidden>', ex)
                box = ex.split("data-scaling>", 1)[1].split("</figure>", 1)[0]
                self.assertEqual(box.count('<svg class="chart lines'), 2)
                sc = data["scaling"]
                metric = sc["y"]
                if preview:                                 # no par: the numbers themselves
                    self.assertIsNone(sc["par"])
                    drawn = [ln for ln in sc["lines"] if sum(1 for q in ln["pts"] if metric in q["m"]) >= 2]
                else:
                    par = next(ln for ln in sc["lines"] if ln["id"] == sc["par"])
                    base = {q["key"]: q["m"].get(metric) for q in par["pts"]}
                    drawn = [ln for ln in sc["lines"]
                             if sum(1 for q in ln["pts"] if metric in q["m"] and base.get(q["key"])) >= 2]
                wide = box.split('data-size="wide"', 1)[1].split("</svg>", 1)[0]
                self.assertEqual(wide.count('<g class="series"'), len(drawn))
                for ln in drawn:
                    self.assertIn(f'data-id="{html.escape(ln["id"])}"', wide)
                if preview:
                    self.assertNotIn('<line class="par-line"', wide)
                    self.assertIn("this task is a preview, so nothing of it is ranked yet", text)
                    self.assertNotIn("the board ranks at", text)
                    self.assertNotIn(", ranked)", text)
                else:
                    self.assertIn('<line class="par-line"', wide)
                    self.assertIn(f"the board ranks at {scored['full']} only", text)
                heads_ = re.findall(r"<th\b[^>]*>(.*?)</th>", ex.split("every design at every point", 1)[1], re.S)
                self.assertEqual([text_of(h) for h in heads_][1:],
                                 [p["full"] + ((" (scored)" if preview else " (ranked)") if p["scored"] else "")
                                  for p in data["points"]])

    def test_shared_lines_and_families_are_explained(self):
        """A line named 'add_n +1' (designs with the same numbers at every point) and a family line ('dadda_ks', one
        fixed-size file per point) are explained under the scaling chart, and only where the page has one."""
        for t in self.several():
            with self.subTest(task=t):
                html_, data = self.page_data(t)
                cap = norm(text_of(section(html_, "explore").split('id="scaling"', 1)[1].split("</figcaption>", 1)[0]))
                lines = data["scaling"]["lines"]
                shared = any(len(ln["names"]) > 1 and not ln["family"] for ln in lines)
                self.assertEqual("stands for that many more designs with the same numbers at every point" in cap, shared)
                fams = sorted(ln["name"] for ln in lines if ln["family"])
                self.assertEqual("of fixed-size baselines, one file per size" in cap, bool(fams))
                for name in fams:
                    self.assertIn(name, cap)

    def test_the_drops_are_said_on_the_page(self):
        """A (design, point) the measurement dropped is named on the page with its reason."""
        for t in self.several():
            with self.subTest(task=t):
                html_, data = self.page_data(t)
                text = norm(text_of(section(html_, "explore")))
                names = {p["key"]: p["full"] for p in data["points"]}
                for e in self.measured(t)["designs"]:
                    for key, why in (e.get("dropped") or {}).items():
                        self.assertIn(f"{e['name']} at {names[key]} ({why})", text)

    def test_hidden_tasks_are_measured_but_not_published(self):
        """matmul and the sorter stay hidden (no page, no data in the output) while their points are measured."""
        for t, how in self.config["tasks"].items():
            if how != "hidden":
                continue
            with self.subTest(task=t):
                self.assertNotIn(f"tasks/{t}/index.html", self.files)
                self.assertFalse(any(p.startswith(f"tasks/{t}/") or p == f"data/tasks/{t}.json" for p in self.files))
                if t in ("matmul", "sorter"):
                    self.assertGreaterEqual(len(self.measured(t)["points"]), 2)

    def test_the_trusted_statement_as_property_cards(self):
        """A task with a properties.json shows one card per property and per definition. Each card's
        Lean block is its declaration cut verbatim from the file properties.json names, and its
        "Open in code" lands on that declaration in the source view (Properties.lean's own page, or
        the trusted module's page). The counter counts the properties proper (not the parameter
        range), and the panel says that statement_iff_properties makes the cards the statement."""
        leansrc = build.leansrc
        shown = 0
        for t in self.listed:
            pj = os.path.join(SVGOLF, "tasks", t, "properties.json")
            if not os.path.isfile(pj):
                continue
            shown += 1
            with self.subTest(task=t), open(pj, encoding="utf-8") as fh:
                info = json.load(fh)
                here = f"tasks/{t}/index.html"
                spec = section(self.files[here].decode("utf-8"), "spec")
                cards = dict(re.findall(r'<details class="prop" id="([^"]+)">(.*?)</details>', spec, re.S))
                for kind, items in (("prop", info["properties"]), ("def", info["definitions"])):
                    for it in items:
                        body = cards.pop(f"prop-{it['name']}" if kind == "prop" else f"def-{it['decl']}")
                        text = build.read_text(it["file"])
                        block = re.search(r'<pre class="code excerpt"[^>]*><code>(.*?)</code></pre>', body, re.S)
                        lean = text_of(block.group(1))
                        self.assertEqual(lean, leansrc.excerpt(text, leansrc.find(text, it["decl"])), it["decl"])
                        self.assertIn(lean, text)
                        href = re.findall(r'<a class="btn[^"]*" href="([^"]+)"', body)[-1]
                        target, _, frag = href.partition("#")
                        self.assertEqual(frag, it["decl"])
                        dest = posixpath.normpath(posixpath.join(posixpath.dirname(here), target))
                        if it["file"] == info["file"]:
                            self.assertEqual(dest, f"tasks/{t}/properties.html")
                        else:
                            self.assertTrue(dest.startswith("trusted/"), dest)
                        self.assertIn(it["decl"], self.pages[dest].ids)
                self.assertEqual(cards, {})
                n = sum(1 for p in info["properties"] if p["kind"] == "property")
                # a task's page states requirements: no proof status on the cards or in the head
                self.assertNotIn("badge-proved", spec)
                self.assertNotIn("badge-todo", spec)
                self.assertNotIn(">Proved ", spec)
                self.assertIn(f'>Properties<span class="props-n">{n}</span>', spec)
                self.assertIn("theorem statement_iff_properties", text_of(spec))
                self.assertIn((f"tasks/{t}/properties.html", info["file"]),
                              {(f"tasks/{t}/properties.html", src) for src, _ in
                               self.pages[f"tasks/{t}/properties.html"].src_blocks})
                with open(build.repo_file(info["file"]), "rb") as fh:
                    self.assertEqual(self.files[f"tasks/{t}/Properties.lean"], fh.read())
        self.assertGreaterEqual(shown, 5)

    def test_a_recorded_reference_names_its_proof(self):
        """A reference record whose proof is not the par design's (the by-hand proof of the same
        design) says which proof it is, and the references table links it from that proof's row."""
        rec = next(r for r in records() if r["task"] == "add" and r["player"] == self.config["reference_player"])
        with open(os.path.join(SVGOLF, "tasks", "add", "reference", "add_n_byhand.lean"), "rb") as fh:
            self.assertEqual(hashlib.sha256(fh.read()).hexdigest(), rec["files"]["lean"]["sha256"])
        page_ = text_of(self.files[f"tasks/add/records/{rec['record_hash']}.html"])
        self.assertIn("the proof of the reference add_n_byhand", page_)
        self.assertIn("by-hand proof", page_)
        refs = section(self.files["tasks/add/index.html"].decode("utf-8"), "references")
        row = next(r for r in refs.split("<tr") if "add_n_byhand</code>" in r)
        self.assertIn(rec["record_hash"][:12], row)
        row = next(r for r in refs.split("<tr") if "<code>add_n</code>" in r)
        self.assertNotIn(rec["record_hash"][:12], row)

    def test_no_internal_why_on_any_page(self):
        """The internal notes of tests/expected.json (`why`) and task.json (`note`, the banlist
        comment where content overrides it) are never rendered; the curated sentences are."""
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)
        pages = {p: norm(text_of(d)) for p, d in self.files.items() if p.endswith(".html")}
        notes = []
        for t in self.listed:
            exp = expected["tasks"].get(t, {})
            for sec in ("references", "baselines", "negatives", "attacks"):
                notes += [(t, sec, stem, e["why"]) for stem, e in exp.get(sec, {}).items() if e.get("why")]
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            notes += [(t, "note", r["sv"], r["note"]) for r in task.get("references", []) if r.get("note")]
        self.assertTrue(notes)
        for t, sec, stem, why in notes:
            w = norm(why)
            for p, text in pages.items():
                self.assertNotIn(w, text, f"{p} shows the internal note of {t} {sec} {stem}")
        for t in self.listed:
            self.assertNotIn("Refute.lean", pages[f"tasks/{t}/index.html"], t)

    def test_every_rejected_design_has_its_curated_sentence(self):
        with open(os.path.join(SVGOLF, "tests", "expected.json"), encoding="utf-8") as fh:
            expected = json.load(fh)
        checked = 0
        for t in self.listed:
            with open(os.path.join(SITE, "content", "attacks", f"{t}.json"), encoding="utf-8") as fh:
                said = json.load(fh)
            page_ = norm(text_of(section(self.files[f"tasks/{t}/index.html"].decode("utf-8"), "does-not-count")))
            exp = expected["tasks"].get(t, {})
            for sec in ("negatives", "attacks"):
                for stem, e in exp.get(sec, {}).items():
                    if e.get("advisory") or e.get("stage") == "unproved":
                        continue
                    with self.subTest(task=t, design=f"{sec}/{stem}"):
                        sentence = said.get(sec, {}).get(stem, "")
                        self.assertTrue(sentence.strip(), f"no curated sentence for {t} {sec}/{stem}")
                        self.assertIn(norm(sentence), page_)
                        self.assertIn(f"{stem}.sv ({sec[:-1]}, stopped at {e['stage']})", page_)
                        checked += 1
                for stem in said.get(sec, {}):
                    self.assertIn(stem, exp.get(sec, {}), f"{t}: a curated sentence for an unknown {sec}/{stem}")
        self.assertGreater(checked, 50)

    def test_every_reference_and_baseline_has_its_curated_description(self):
        for t in self.listed:
            with open(os.path.join(SITE, "content", "tasks", f"{t}.json"), encoding="utf-8") as fh:
                info = json.load(fh)
            html_ = self.files[f"tasks/{t}/index.html"].decode("utf-8")
            self.assertTrue(info.get("title") and info.get("subtitle"), t)
            self.assertIn(f"<h1>{html.escape(info['title'])} ", html_)
            data = json.loads(self.files[f"data/tasks/{t}.json"])
            for kind, sec in (("references", "references"), ("baselines", "baselines")):
                text = norm(text_of(section(html_, sec)))
                for item in data[kind]:
                    with self.subTest(task=t, design=item["stem"]):
                        d = info[kind].get(item["stem"], "")
                        self.assertTrue(d.strip())
                        self.assertEqual(item["description"], d.strip())
                        self.assertIn(norm(d), text)

    def test_rejected_designs_are_shown_without_their_comments(self):
        html_ = self.files["tasks/add/index.html"].decode("utf-8")
        part = section(html_, "does-not-count")
        self.assertIn("slang_initial_comb.sv", part)
        self.assertNotIn("data-src", part)
        self.assertNotIn("<span class=\"hl-com\">", part)
        self.assertIn("initial cout", text_of(part))

    def test_a_licensed_rejected_design_keeps_its_notices(self):
        # The SRT attacks are adapted from Apache-2.0 WITH SHL-2.1 code: its copyright and change
        # notices must travel with the code, so these designs are shown with their comments.
        part = text_of(section(self.files["tasks/fdivp/index.html"].decode("utf-8"), "does-not-count"))
        self.assertIn("srt_no_cin.sv", part)
        self.assertIn("SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1", part)
        self.assertIn("Copyright (C) 2021-26 Harvey Mudd College", part)
        self.assertIn("Changes to the Wally code", part)
        self.assertIn("tasks/fdivp/reference/LICENSES/", part)

    def test_an_mit_rejected_design_keeps_its_notice(self):
        # The sorter's attacks are copies of MIT-licensed code (andrewpeck/cell-sort): the MIT notice
        # must be included in every copy, so they are shown with their comments too.
        part = text_of(section(self.files["tasks/sorter/index.html"].decode("utf-8"), "does-not-count"))
        self.assertIn("token_self.sv", part)
        self.assertIn("Copyright (c) 2024-2025 Andrew Peck", part)
        self.assertIn("Permission is hereby granted, free of charge", part)
        self.assertIn("The above copyright notice and this permission notice shall be included", part)

    def test_submit_without_a_public_repository(self):
        files = self.files
        if self.config["repo_url"] is not None:
            config = build.load_config()
            config["repo_url"] = None
            files = build.build_site(offline=True, config=config).files
        for t in self.listed:
            with self.subTest(task=t):
                part = text_of(section(files[f"tasks/{t}/index.html"].decode("utf-8"), "submit"))
                self.assertIn("Public submissions open when the svGolf repository is published", part)
                self.assertNotIn("pull request", part)
                self.assertNotIn("git clone", part)
                self.assertNotIn("--data-dir", part)
                self.assertIn(f"leaderboard/data/{t}/", part)
                self.assertIn("--sandbox require", part)
                self.assertIn("--sandbox auto", part)
                self.assertIn(f"check.py tasks/{t} ", part)
        self.assertNotIn("pull request", files["llms.txt"].decode("utf-8"))

    def test_home_defines_ls_sv_with_a_link_where_it_first_appears(self):
        html_ = self.files["index.html"].decode("utf-8")
        first = html_.index("ls-sv")
        self.assertTrue(html_[:first].endswith('">'), "the first ls-sv is a link text")
        self.assertIn("formal semantics of SystemVerilog", text_of(html_[first:first + 400]))

    def test_home_does_not_overclaim_the_post_synthesis_check(self):
        home = norm(text_of(self.files["index.html"]))
        about = norm(text_of(self.files["about.html"]))
        for text in (home, about):
            self.assertNotIn("the circuit that was proved is the circuit that was scored", text)
            self.assertNotIn("fixed set of vectors", text)
            self.assertNotIn("closes the gap", text)
        self.assertIn("sample of input vectors", home)
        self.assertIn("sampling, not a proof", home)
        self.assertIn("salted in competition runs", home)

    def test_two_builds_are_byte_identical(self):
        other = os.path.join(self.tmp.name, "again")
        env = dict(os.environ, PYTHONHASHSEED="4242")   # a different hash seed: set order must not leak
        proc = subprocess.run([sys.executable, BUILD_PY, "--offline", "--out", other], capture_output=True,
                              text=True, env=env, cwd=SVGOLF)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        again = read_tree(other)
        self.assertEqual(sorted(again), sorted(self.files))
        self.assertEqual([p for p in sorted(again) if again[p] != self.files[p]], [])

    def test_no_denylisted_string_in_the_output(self):
        # (a public configuration keeps its denylist outside the repository: `build.py --denylist`)
        deny = [w.lower() for w in self.config["denylist"] if isinstance(w, str)]
        for path, data in self.files.items():
            text = data.decode("utf-8", errors="replace").lower()
            for w in deny:
                self.assertNotIn(w, text, f"{path} contains {w!r}")

    def test_no_internal_marker_in_the_sites_own_text(self):
        """The internal markers (names, work-package codes, review rounds) do not occur in what the
        site writes itself: every page without its verbatim <pre data-src> blocks and without what
        players wrote, plus the generated data and llms.txt (the files offered byte for byte are the
        repository's)."""
        markers = [e for e in self.config["denylist"] if isinstance(e, dict)]
        players = set()
        for r in records():
            players.update([r["player"], *r["assisted_by"], r.get("notes") or ""])
        for path, data in sorted(self.files.items()):
            if not (path.endswith(".html") or path.startswith("data/") or path == "llms.txt"):
                continue
            text = data.decode("utf-8")
            if path.endswith(".html"):
                text = re.sub(r'<pre[^>]* data-src="[^"]*"[^>]*>.*?</pre>', "", text, flags=re.S)
                text = html.unescape(text)
            for p in sorted(players, key=len, reverse=True):
                if p:
                    text = text.replace(p, "")
            text = text.lower()
            for m in markers:
                if path in m.get("allow", {}):
                    continue
                self.assertNotIn(m["text"].lower(), text, f"{path} contains the internal marker {m['text']!r}")


class GuardTest(unittest.TestCase):
    """The build's own guards fire."""

    def build(self, **kw):
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return build.build_site(offline=True, **kw)

    def test_strict_build_passes(self):
        site = self.build(strict=True)
        self.assertEqual(site.warnings, [])

    def test_a_denylist_hit_fails_the_build(self):
        config = build.load_config()
        config["denylist"] = config["denylist"] + ["Pareto frontier"]
        with self.assertRaises(build.BuildError) as e:
            self.build(config=config)
        self.assertIn("Pareto frontier", str(e.exception))

    def test_a_stale_redaction_fails_the_build(self):
        config = build.load_config()
        config["redact"] = config["redact"] + [{"file": "svgolf/README.md", "text": "no such phrase, ever", "with": ""}]
        with self.assertRaises(build.BuildError):
            self.build(config=config)

    def test_a_flow_mismatch_fails_unless_offline(self):
        real = lb.current_flow
        try:
            lb.current_flow = lambda svgolf=None: dict(pinned_flow(), yosys=None)   # no Yosys on PATH
            with self.assertRaises(build.BuildError) as e:
                with contextlib.redirect_stderr(io.StringIO()):
                    build.build_site(offline=False)
            self.assertIn("yosys", str(e.exception))
            lb.current_flow = lambda svgolf=None: dict(pinned_flow())
            with contextlib.redirect_stderr(io.StringIO()):
                build.build_site(offline=False)
        finally:
            lb.current_flow = real

    def test_a_task_without_content_uses_its_readme_and_fails_strict(self):
        real = build.CONTENT
        with tempfile.TemporaryDirectory() as tmp:
            content = os.path.join(tmp, "content")
            shutil.copytree(os.path.join(SITE, "content"), content)
            os.remove(os.path.join(content, "tasks", "add.md"))
            try:
                build.CONTENT = content
                site = self.build()
                self.assertEqual(len(site.warnings), 1)
                self.assertIn("add", site.warnings[0])
                self.assertIn(b"The warm-up challenge", site.files["tasks/add/index.html"])  # the README intro
                with self.assertRaises(build.BuildError):
                    self.build(strict=True)
            finally:
                build.CONTENT = real

    def with_content(self, edit, **kw):
        """Build with a copy of site/content changed by `edit(content_dir)`."""
        real = build.CONTENT
        with tempfile.TemporaryDirectory() as tmp:
            content = os.path.join(tmp, "content")
            shutil.copytree(os.path.join(SITE, "content"), content)
            edit(content)
            try:
                build.CONTENT = content
                return self.build(**kw)
            finally:
                build.CONTENT = real

    def test_an_internal_marker_in_a_curated_text_fails_the_build(self):
        def edit(content):
            path = os.path.join(content, "attacks", "clmul.json")
            with open(path, encoding="utf-8") as fh:
                said = json.load(fh)
            said["negatives"]["drop_top"] += " Found in the round-zz review (QQ-T)."
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(said, fh)
        config = build.load_config()
        config["denylist"] = config["denylist"] + [{"text": t, "scope": "site-text", "why": "a test"}
                                                   for t in ("QQ-", "round-zz")]
        with self.assertRaises(build.BuildError) as e:
            self.with_content(edit, config=config)
        self.assertIn("tasks/clmul/index.html: contains the internal marker 'QQ-'", str(e.exception))
        self.assertIn("'round-zz'", str(e.exception))

    def test_a_missing_curated_sentence_warns_and_fails_strict(self):
        def edit(content):
            path = os.path.join(content, "attacks", "mul.json")
            with open(path, encoding="utf-8") as fh:
                said = json.load(fh)
            del said["negatives"]["drop_carry"]
            said["negatives"]["no_such_design"] = "A design the task does not have."
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(said, fh)
        site = self.with_content(edit)
        self.assertEqual(len(site.warnings), 2, site.warnings)
        self.assertTrue(any("negative drop_carry" in w for w in site.warnings))
        self.assertTrue(any("no_such_design" in w for w in site.warnings))
        page_ = site.files["tasks/mul/index.html"].decode("utf-8")
        self.assertIn("drop_carry.sv", page_)                       # still listed, without a sentence
        self.assertNotIn("refuted in negative", page_)              # never the internal note instead
        with self.assertRaises(build.BuildError):
            self.with_content(edit, strict=True)

    def test_internal_markers_spare_verbatim_files_and_player_fields(self):
        deny = ["/nowhere/", {"text": "QQ-", "scope": "site-text"}, {"text": "zz-", "scope": "site-text"}]
        files = {
            "a.html": b'<p>ok</p><pre class="code" data-src="x.sv"><code>// QQ-G note</code></pre>',
            "b.html": b"<p>assisted by ZZ-5 (Example)</p>",
            "c.sv": b"// QQ-G note\n",
            "d.json": b'{"assisted_by": ["ZZ-5 (Example)"]}',
        }
        self.assertEqual(build.check_denylist(files, deny, copies={"c.sv"}, player_text={"ZZ-5 (Example)"}), [])
        hits = build.check_denylist(files, deny, copies=set(), player_text=set())
        self.assertEqual(sorted(h.split(":")[0] for h in hits), ["b.html", "c.sv", "d.json"])
        files["e.html"] = b"<p>see QQ-P</p>"
        hits = build.check_denylist(files, deny, copies={"c.sv"}, player_text={"ZZ-5 (Example)"})
        self.assertEqual(hits, ["e.html: contains the internal marker 'QQ-' (denylist, scope site-text)"])
        files["c.sv"] = b"/nowhere/someone\n"                     # a plain entry: everywhere, copies too
        hits = build.check_denylist(files, deny, copies={"c.sv"}, player_text={"ZZ-5 (Example)"})
        self.assertIn("c.sv: contains the denylisted '/nowhere/'", hits)

    def test_a_stale_marker_allowance_fails_the_build(self):
        config = build.load_config()
        config["denylist"] = config["denylist"] + [{"text": "zz-never-written", "scope": "site-text", "why": "a test",
                                                    "allow": {"about.html": "a test"}}]
        with self.assertRaises(build.BuildError) as e:
            self.build(config=config)
        self.assertIn("about.html: config.json allows the internal marker 'zz-never-written' here", str(e.exception))

    def test_an_all_redaction_replaces_every_occurrence_and_goes_stale_at_zero(self):
        config = build.load_config()
        config["redact"] = config["redact"] + [{"file": "svgolf/README.md", "text": "Yosys", "with": "Yosys", "all": True}]
        self.build(config=config)
        config["redact"][-1]["text"] = "no such phrase, ever"
        with self.assertRaises(build.BuildError) as e:
            self.build(config=config)
        self.assertIn("at least once", str(e.exception))

    def test_submit_with_a_public_repository(self):
        config = build.load_config()
        config["repo_url"] = "https://example.org/someone/lean-surfaces.git"
        site = self.build(config=config)
        page_ = site.files["tasks/clmul/index.html"].decode("utf-8")
        part = text_of(section(page_, "submit"))
        self.assertIn("git clone https://example.org/someone/lean-surfaces.git", part)
        # inside lean-surfaces svGolf is a directory of the clone; standalone it is the clone
        self.assertIn("cd lean-surfaces/svgolf\n" if build.LAYOUT == "inside" else "cd lean-surfaces\n", part)
        self.assertIn("pull request", part)
        self.assertIn("leaderboard/data/clmul/", part)
        self.assertNotIn("Public submissions open when", part)
        self.assertIn("pull request", site.files["llms.txt"].decode("utf-8"))

    def test_strip_sv_comments(self):
        text = ('// header: QQ-G, Someone\n/* block\n   comment */\nmodule m(input a, output y);\n'
                '  assign y = a; // trailing\n\n\n  // only a comment\n  initial $display("// not a comment");\n'
                'endmodule\n// tail\n')
        self.assertEqual(build.strip_sv_comments(text),
                         'module m(input a, output y);\n  assign y = a;\n\n'
                         '  initial $display("// not a comment");\nendmodule\n')


if __name__ == "__main__":
    unittest.main()
