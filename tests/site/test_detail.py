"""The detail pages of the site: one per record and one per proved reference without a record (PLAN4 3b step 3):
the overview (Area, Performance and Score cards, with their beats/matches lines once there is a field), the sources
across the page, then two columns (the netlist card, whose tabs are the schematic of the display instance, the
critical path and the cells, and under it a record's checker detail; beside them the record's or the reference's
facts), then the area-time plot and reproduce. Built once with --offline. The order and the columns were decided
2026-11-09: the code before the schematic, the critical path a tab under it, the record and the proof in a second
column as on the task page.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)

No network, no Yosys, no Lean: the schematic data are the committed files of site/schematics/.
"""

import contextlib
import hashlib
import html
import importlib.util
import io
import json
import os
import posixpath
import re
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")


def load(name, path):
    sys.path.insert(0, SITE)
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


build = load("svgolf_site_build_detail", os.path.join(SITE, "build.py"))
lb = build.lb
sys.path.insert(0, HERE)
from pdkview import view_of  # noqa: E402  (a page as one library's reader sees it)


def read_json(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def norm(s):
    """Every run of whitespace (the thin spaces of grouped numbers included) as one space."""
    return re.sub(r"\s+", " ", s)


def text_of(h):
    return norm(html.unescape(re.sub(r"<[^>]+>", "", h)))


def section(page_html, sid):
    """The HTML of the element with id `sid` (to its matching close tag, by nesting of the same tag)."""
    m = re.search(r'<(section|div|article)\b[^>]*\bid="' + re.escape(sid) + r'"', page_html)
    if not m:
        return ""
    tag, start, depth, i = m.group(1), m.start(), 0, m.start()
    for t in re.finditer(r"<(/?)" + tag + r"\b", page_html[start:]):
        depth += -1 if t.group(1) else 1
        if depth == 0:
            return page_html[start:start + t.end()]
    return page_html[start:]


def shown_refs(task):
    """The task.json references the site shows (decided 2026-11-12): the proofs of par's design, the one design
    leaderboard/par.json names; every other reference is an entry, shown once a player's record holds it."""
    par = lb.par_names(os.path.join(SVGOLF, "tasks"), task)
    return [r for r in task.get("references", [])
            if lb.sha256_file(os.path.join(SVGOLF, "tasks", task["name"], r["sv"])) in par]


def records():
    out = []
    data = os.path.join(SVGOLF, "leaderboard", "data")
    for t in sorted(os.listdir(data)):
        for f in sorted(os.listdir(os.path.join(data, t))):
            if f.endswith(".json"):
                out.append(read_json(os.path.join(data, t, f)))
    return out


class DetailTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            cls.site = build.build_site(offline=True)
        cls.files = cls.site.files
        cls.config = build.load_config()
        # a preview has no detail pages (build.reference_page): its references are rows of its task page
        cls.listed = [t for t, how in cls.config["tasks"].items() if how not in ("hidden", "preview")]
        cls.previews = [t for t, how in cls.config["tasks"].items() if how == "preview"]
        cls.recs = [r for r in records() if r["task"] in cls.listed]

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def page(self, path, pdk="sky130"):
        """The page as the reader of the `pdk` view sees it (the library selector: sky130 by default, as without
        JavaScript; `pdkview.view_of`)."""
        return view_of(self.files[path].decode("utf-8"), pdk)

    def detail_pages(self):
        """(task, site path, record or None, reference stem or None) of every detail page there should be."""
        out = []
        for t in self.listed:
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            recorded = set()
            for r in self.recs:
                if r["task"] == t:
                    out.append((t, f"tasks/{t}/records/{r['record_hash']}.html", r, None))
                    if r["player"] == self.config["reference_player"]:
                        recorded.add((r["files"]["sv"]["sha256"], r["files"]["lean"]["sha256"]))
            for ref in shown_refs(task):
                stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                with open(os.path.join(SVGOLF, "tasks", t, ref["sv"]), "rb") as a, \
                        open(os.path.join(SVGOLF, "tasks", t, ref["lean"]), "rb") as b:
                    key = (hashlib.sha256(a.read()).hexdigest(), hashlib.sha256(b.read()).hexdigest())
                if key not in recorded:
                    out.append((t, f"tasks/{t}/reference/{stem}.html", None, stem))
        return out

    def test_every_record_and_every_reference_has_a_detail_page(self):
        pages = self.detail_pages()
        self.assertGreaterEqual(len(pages), 18)
        for t, path, rec, stem in pages:
            with self.subTest(page=path):
                self.assertIn(path, self.files)
        for t in ("fdivp", "aes_sbox"):        # seeded under the current ppa_version (PLAN4 3b step 4)
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            mine = [r for r in self.recs if r["task"] == t and r["player"] == self.config["reference_player"]]
            # (2026-11-12) par's design alone is recorded under the reference handle: one proof of it here
            self.assertEqual(len(mine), len(shown_refs(task)), t)
            for r in mine:
                self.assertEqual(r["ppa"]["ppa_version"], lb.ppa_identity()["ppa_version"])

    def test_the_task_page_links_every_reference_to_its_page(self):
        for t in self.listed:
            with self.subTest(task=t):
                task_html = self.page(f"tasks/{t}/index.html")
                refs = section(task_html, "references")
                for _, path, rec, stem in self.detail_pages():
                    if not path.startswith(f"tasks/{t}/"):
                        continue
                    href = posixpath.relpath(path, f"tasks/{t}")
                    if stem is not None or (rec and rec["player"] == self.config["reference_player"]):
                        self.assertIn(f'href="{href}"', refs, path)
                # the charts' reference marks open the same pages
                for m in re.finditer(r'<a href="([^"]+)" aria-label="[^"]*"><g class="mark[^"]*" data-kind="reference"',
                                     task_html):
                    self.assertTrue(m.group(1).startswith(("reference/", "records/")), m.group(1))

    def test_a_preview_has_no_detail_pages(self):
        """A preview ranks nothing: no record page, no reference page; the task page's references, its charts' marks
        and its data link each reference to its own row there (`#ref-<stem>`), and no page of the task says it is
        ranked."""
        if not self.previews:                       # none since matmul and the sorter rank (2026-11-08)
            self.skipTest("config.json lists no preview")
        for t in self.previews:
            with self.subTest(task=t):
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                pages = [p for p in self.files if p.startswith((f"tasks/{t}/records/", f"tasks/{t}/reference/"))
                         and p.endswith(".html")]
                self.assertEqual(pages, [])
                task_html = self.page(f"tasks/{t}/index.html")
                refs = section(task_html, "references")
                for ref in shown_refs(task):
                    stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                    self.assertIn(f'id="ref-{stem}"', refs)
                    self.assertNotIn(f'href="reference/{stem}.html"', task_html)
                for m in re.finditer(r'<a href="([^"]+)" aria-label="[^"]*"><g class="mark[^"]*" data-kind="reference"',
                                     task_html):
                    self.assertRegex(m.group(1), r"^index\.html#ref-[A-Za-z0-9_]+$")
                for path in (p for p in self.files if p.startswith(f"tasks/{t}/") and p.endswith(".html")):
                    self.assertNotIn("· ranked", text_of(self.page(path)), path)

    def test_every_detail_page_has_its_sections_in_order(self):
        """The order decided 2026-11-09: the overview, then the code, then the netlist (the schematic, the
        critical path, the cells), the area-time plot below the columns; it was dashboard, plot, schematic, critical
        path, cells, ..., sources, reproduce, with the code second to last. A record's facts and proof come before
        its checker and post-synthesis check (on a phone, one column: the player, the date and the notes before the
        checker detail; review 2026-11-09, L2)."""
        for t, path, rec, stem in self.detail_pages():
            order = ("dashboard", "sources", "schematic", "critical-path", "cells")
            order += ("record", "proof", "checker", "postsynth") if rec else ("reference",)
            order += ("area-time", "reproduce")
            with self.subTest(page=path):
                h = self.page(path)
                if "No ranked numbers to show" in text_of(section(h, "dashboard")):
                    order = tuple(o for o in order if o != "area-time")
                at = [h.find(f'id="{sid}"') for sid in order]
                self.assertTrue(all(a >= 0 for a in at), dict(zip(order, at)))
                self.assertEqual(at, sorted(at))
                self.assertIn('src="../../../charts.js"', h)
                self.assertNotRegex(h, r"(?<![\d\u202f])\b1 cells\b")       # "1 cell" (review 2026-11-09, N2)

    def test_the_code_and_the_netlist_beside_the_facts(self):
        """The sources across the page under the overview (in the main column the code box showed 81 columns at
        1280 px and cut lines it shows whole across the page: review 2026-11-09, M1), then two columns as on the task
        page: the main one holds the netlist card and, under it, a record's checker card and a combinational record's
        post-synthesis facts (`more`, beside the rest of the side column); the side one the record and the proof (a
        record's page) or the reference's facts. A clocked record's post-synthesis table, the area-time plot and
        reproduce come after the columns (they need the page's width)."""
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            main, side, more = section(h, "main-col"), section(h, "side-col"), section(h, "more-col")
            with self.subTest(page=path):
                self.assertTrue(main and side, "no columns")
                self.assertLess(h.index('id="sources"'), h.index('id="main-col"'))
                self.assertLess(h.index('id="main-col"'), h.index('id="side-col"'))
                for sid in ("netlist", "schematic", "critical-path", "cells"):
                    self.assertIn(f'id="{sid}"', main, sid)
                for sid in (("record", "proof") if rec else ("reference",)):
                    self.assertIn(f'id="{sid}"', side, sid)
                    self.assertNotIn(f'id="{sid}"', main, sid)
                for sid in ("dashboard", "sources", "area-time", "reproduce"):
                    self.assertNotIn(f'id="{sid}"', main + side + more, sid)
                if rec is None:
                    self.assertEqual(more, "")
                    continue
                self.assertLess(h.index('id="side-col"'), h.index('id="more-col"'))
                self.assertIn('id="checker"', more)
                clocked = isinstance(rec["postsynth"].get("points"), list)
                self.assertEqual('id="postsynth"' in more, not clocked)     # a clocked table needs the page's width
                src = section(h, "sources")
                self.assertLess(src.index("<pre"), src.index("<details"))        # the design file, then the proof
                # the box's download link downloads, under the name the box's head shows (L8)
                name = rec["files"]["sv"]["name"] if rec else f"{stem}.sv"
                self.assertRegex(src, r'<a class="codebox-dl" href="[^"]+\.sv" download="' + re.escape(name) + '">')
                if rec and rec["player"] != self.config["reference_player"]:
                    self.assertIn('id="diff"', h)       # a diff card, or a first submission's "previous frontier: none"
                self.assertIn('<span class="codebox-name">' + html.escape(
                    rec["files"]["sv"]["name"] if rec else f"{stem}.sv") + "</span>", src)

    def test_the_netlist_card_has_three_tabs(self):
        """The schematic, the critical path and the cells are the three tabs of one card (site.js; without the
        script, three panes under their titles): each pane a section with the id the page's links use. The overview
        links its cells and critical-path numbers to their tabs."""
        tasks = {t.name: t for t in self.tasks()}
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            card = section(h, "netlist")
            with self.subTest(page=path):
                nav = re.search(r'<nav class="tabs-nav"[^>]*>(.*?)</nav>', card, re.S)
                self.assertIsNotNone(nav)
                self.assertEqual(re.findall(r'<a href="#([^"]+)"', nav.group(1)), ["schematic", "critical-path", "cells"])
                self.assertEqual(text_of(nav.group(1)), "SchematicCritical pathCells")
                for sid in ("schematic", "critical-path", "cells"):
                    self.assertIn(f'<section class="tabs-pane" id="{sid}">', card)
                # without the script no tab is marked as chosen: the panes all stand there (review 2026-11-09, L6)
                self.assertNotIn('class="on"', nav.group(0))
                dash = section(h, "dashboard")
                for href in re.findall(r'<a href="#([^"]+)"', dash):
                    self.assertIn(href, ("cells", "critical-path", "area-time"))
                # the rows that describe the area-time plot link to it, further down the page (L3)
                if "<dt>on this page</dt>" in dash:
                    self.assertIn('href="#area-time"', dash)
                # each pane says the size it shows, as the three cards' heads did (L5)
                scored = f"at {build.point_text(tasks[t].point)} · scored"
                for sid in ("critical-path", "cells"):
                    label = re.search(r'<p class="label pane-scale">(.*?)</p>', section(card, sid))
                    self.assertEqual(text_of(label.group(1)), norm(scored))

    def test_the_cards_show_the_ranked_numbers(self):
        """The Area, Performance and Score cards: the record's own sky130 columns (a reference without a record: its
        golden), exact. While the task has no other player the overview says so once, under the cards, and draws no
        beats/matches line (it drew an empty one on every card, four times on a page, until the request of 2026-11-09
        "this overview can be cleaned up visually")."""
        tasks = {t.name: t for t in self.tasks()}
        shown = 0
        for t, path, rec, stem in self.detail_pages():
            dash = text_of(section(self.page(path), "dashboard"))
            if rec is not None and lb.statement_mismatch(rec, lb.current_statement(tasks[t].task)):
                cols = None        # checked under another statement, or before records named theirs: not ranked
            elif rec is not None and isinstance(rec.get("ppa"), dict) and rec["ppa"].get("available"):
                cols = lb.ranked_columns(rec)
            else:
                d = next((d for d in tasks[t].designs if d["kind"] == "reference" and d["stem"] == stem), None)
                cols = ({"area_e4um2": build.combined.e4um2(d["m"]["area_um2"]), "time_ps": d["m"]["time_ps"]}
                        if d and "area_um2" in d["m"] else None)
            with self.subTest(page=path):
                if cols is None:
                    self.assertIn("No ranked numbers to show", dash)
                    continue
                shown += 1
                for label in ("Area", "Performance · time", "Score · area × time", "vs par", "board"):
                    self.assertIn(label, dash)
                # "on this page" and "Pareto" are rows only when the plot has other designs; alone, the note says so
                # once (each card said "the only design with sky130 numbers")
                alone = len(build.plotted(tasks[t])) == 1
                self.assertNotIn("the only design with sky130 numbers", dash)
                self.assertEqual(dash.count("This design is the only one with sky130 numbers on this page"), int(alone))
                if not alone:
                    for label in ("on this page", "Pareto"):
                        self.assertIn(label, dash)
                self.assertNotIn("badge", section(self.page(path), "dashboard"))         # no "ranked" pill per card
                self.assertIn(norm(f"{build.grouped(lb.fmt_um2(cols['area_e4um2']))} µm² exactly"), dash)
                self.assertIn(norm(f"{cols['time_ps']:,}".replace(",", " ")) + "ps", dash)
                score = build.combined.fmt(build.combined.um2ns(cols["area_e4um2"] * cols["time_ps"]))
                self.assertIn(norm(score), dash)
                others = {r["player"] for r in self.recs if r["task"] == t and r["player"] != self.config["reference_player"]
                          and (rec is None or r["player"] != rec["player"])}
                n = int(re.search(r"at this revision \((\d+) players?, \d+ records?\)", dash).group(1))
                self.assertLessEqual(n, len(others))
                if not others:
                    self.assertIn("(0 players, 0 records)", dash)
                if n == 0:        # the tutorial is named so (decided 2026-11-12), every other task by its name
                    named = "the tutorial" if self.config["tasks"].get(t) == "tutorial" else t
                    self.assertEqual(dash.count(f"No other player has a ranked record on {named} yet"), 1)
                    self.assertNotIn("Beats", dash)
                    self.assertNotIn('class="meter', section(self.page(path), "dashboard"))
                else:
                    self.assertNotIn("No other player has a ranked record", dash)
                    # the count line under each card's meter; "Beats x% · matches y%" said it again (gone 2026-11-11)
                    self.assertNotIn("Beats", dash)
                    self.assertEqual(len(re.findall(r"\d+ of \d+ other players? beaten, \d+ equal\.", dash)), 3)
        self.assertGreaterEqual(shown, 15)

    def test_a_record_page_is_titled_by_who_made_it(self):
        """A record page's title (decided 2026-11-11): who made the record, on which task, and when, "{player} on {task}
        · {date}" ("{stem} on {task} · reference" for a proved reference's record), its hash a chip of the tag row; the
        browser's <title> "{player} on {task} · record {hash, first 12}", unique per page. No score in either: the
        score differs by course, and the title cannot switch with the view."""
        titles = []
        for t, path, rec, stem in self.detail_pages():
            if rec is None:
                continue
            raw = self.files[path].decode("utf-8")
            h1 = text_of(re.search(r"<h1\b[^>]*>(.*?)</h1>", raw, re.S).group(1)).strip()
            title = html.unescape(re.search(r"<title>(.*?)</title>", raw, re.S).group(1))
            titles.append(title)
            with self.subTest(page=path):
                self.assertNotIn("µm²·ns", h1 + title)
                self.assertNotIn("µm", h1 + title)
                h12 = rec["record_hash"][:12]
                on = "the tutorial" if self.config["tasks"].get(t) == "tutorial" else t       # (decided 2026-11-12)
                if rec["player"] == self.config["reference_player"]:
                    task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                    stems = {posixpath.splitext(posixpath.basename(r["sv"]))[0]: r for r in task["references"]}
                    mine = [st for st, r in stems.items()
                            if (lb.sha256_file(os.path.join(SVGOLF, "tasks", t, r["sv"])),
                                lb.sha256_file(os.path.join(SVGOLF, "tasks", t, r["lean"])))
                            == (rec["files"]["sv"]["sha256"], rec["files"]["lean"]["sha256"])]
                    who = mine[0] if mine else rec["player"]
                    self.assertEqual(h1, f"{who} on {on} · " + ("reference" if mine else rec["submitted_at"][:10]))
                else:
                    who = rec["player"]
                    self.assertEqual(h1, f"{rec['player']} on {on} · {rec['submitted_at'][:10]}")
                self.assertEqual(title, f"{who} on {on} · record {h12} | svGolf")
                tags = re.search(r'<p class="head-tags">(.*?)</p>', raw, re.S).group(1)
                self.assertIn(f'<span class="badge badge-plain">record {h12}</span>', tags)
        self.assertEqual(len(titles), len(set(titles)))

    def test_a_record_page_folds_what_is_for_checking(self):
        """The record page (decided 2026-11-11) shows what a reader reads and folds what is for checking: the record's
        sha256 rows under "hashes", the checker's versions and hashes under the versions the record names, a clocked
        record's run facts under "the run: ..." (its table of points stays shown); a clocked record's post-synthesis
        check says its verdict first."""
        clocked = 0
        for t, path, rec, stem in self.detail_pages():
            if rec is None:
                continue
            raw = self.files[path].decode("utf-8")
            with self.subTest(page=path):
                card = section(raw, "record")
                shown, _, fold = card.partition("<details><summary>hashes</summary>")
                self.assertTrue(fold, "no closed hashes fold")
                for full in (rec["record_hash"], rec["files"]["sv"]["sha256"], rec["files"]["lean"]["sha256"]):
                    self.assertIn(full, text_of(fold))
                    self.assertNotIn(full, text_of(shown))          # (the download links' paths hold the hash)
                for row in ("task", "player", "assisted by", "submitted", "notes", "scoring point"):
                    self.assertIn(f"<dt>{row}</dt>", shown)
                chk = section(raw, "checker")
                m = re.search(r"<details><summary>([^<]*)</summary>(.*?)</details>", chk, re.S)
                self.assertIsNotNone(m)
                self.assertTrue(m.group(1).endswith("the checker: versions and hashes"), m.group(1))
                if rec["checker"].get("yosys"):
                    self.assertTrue(m.group(1).startswith("Yosys "), m.group(1))
                self.assertIn("<dt>svGolf revision</dt>", m.group(2))
                self.assertNotIn("svGolf revision", chk[:m.start()])
                if isinstance(rec["postsynth"].get("points"), list):
                    clocked += 1
                    ps = section(raw, "postsynth")
                    body = ps.split('<h2 class="card-title">', 1)[1].split("</div></div>", 1)[1]
                    self.assertTrue(body.startswith("<p>The check found "), body[:80])
                    run = re.search(r"<details><summary>the run: mode, seeds, stimulus, salt, the scored netlist's "
                                    r"sha256</summary>(.*?)</details>", ps, re.S)
                    self.assertIsNotNone(run)
                    self.assertIn("<dt>mode</dt>", run.group(1))
                    self.assertNotIn("<dt>mode</dt>", ps[:run.start()])
                    self.assertIn("<table", ps[run.end():])
        self.assertGreaterEqual(clocked, 1)

    def test_the_overview_is_quiet(self):
        """The request "this overview can be cleaned up visually" (2026-11-09), second round: every card has the
        same five parts (label, number, the line under it, the field's line, the body), so that side by side they
        line up; a big number's digit groups are narrow spaces in the text face, not a whole monospace figure each;
        par's name and number are a quiet line of their own, its name a link, no code pill; under the cards one
        line at most (the empty field), the definitions folded under one disclosure; "1 other player", singular."""
        for t, path, rec, stem in self.detail_pages():
            dash = section(self.page(path), "dashboard")
            if "No ranked numbers to show" in text_of(dash):
                continue
            with self.subTest(page=path):
                for part in ('class="label"', 'class="big"', 'class="sub"', 'class="mfield"', 'class="mbody"'):
                    self.assertEqual(dash.count(part), 3, part)
                for big in re.findall(r'<p class="big">(.*?)</p>', dash):
                    self.assertNotIn(" ", re.sub(r'<span class="g"> </span>', "", big))
                self.assertNotIn("<code>", "".join(re.findall(r'<dt>vs par</dt><dd>(.*?)</dd>', dash)))
                for v in re.findall(r'<dt>vs par</dt><dd>(.*?)</dd>', dash):
                    if "is par" not in v and "no par" not in v:
                        self.assertRegex(v, r'<span class="mpar"><a href="[^"#][^"]*">[^<]+</a> · ')
                note = dash[dash.index('<div class="dash-note">'):]
                self.assertIn('<details class="reveal"><summary>how these numbers are measured and compared</summary>',
                              note)
                visible = re.sub(r"<details.*?</details>", "", note, flags=re.S)
                self.assertLessEqual(len(re.findall(r"<p\b", visible)), 1)
                self.assertNotRegex(text_of(dash), r"\b1 other players")
                self.assertNotIn("Of 1 other", text_of(dash))
                # the board's line gives the four counts; a definition in brackets after "0 beaten" read as a claim,
                # so the four words are defined once, in the folded note (review 2026-11-09, L4)
                self.assertNotIn("beaten (", text_of(dash))
                if "On the board, of" in text_of(dash):
                    self.assertIn("On the board, another player is beaten when this design dominates every record of "
                                  "theirs", text_of(dash))
                self.assertIn("never stored in a record and never used by the ranking", text_of(dash))     # L5

    def tasks(self):
        if not hasattr(self.__class__, "_tasks"):
            with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.__class__._tasks = build.collect(build.Site(build.load_config()), True)
        return self.__class__._tasks

    def test_references_and_baselines_never_enter_the_field(self):
        """The field counts only the players' ranked records: with none in the repository every page says 0 players,
        although every page draws references and baselines."""
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            m = re.search(r"at this revision \((\d+) players?, (\d+) records?\)", text_of(section(h, "dashboard")))
            if not m:
                continue
            players = {r["player"] for r in self.recs if r["task"] == t and r["player"] != self.config["reference_player"]
                       and (rec is None or r["player"] != rec["player"])}
            with self.subTest(page=path):
                self.assertLessEqual(int(m.group(1)), len(players))
                if not players:
                    self.assertEqual(m.group(1), "0")

    def test_the_plot_rings_this_design_among_the_task_designs(self):
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            box = section(h, "area-time")
            if not box:
                continue
            with self.subTest(page=path):
                self.assertEqual(len(re.findall(r'class="mark subject ', box)) // 2 >= 1, True)
                self.assertIn('class="halo"', box)
                self.assertIn("this design", box)
                self.assertNotIn("<a href=\"#\"", box)
                for href in re.findall(r'<a href="([^"]+)" aria-label', box):
                    self.assertFalse(href.startswith(("http:", "https:", "/")), href)

    def test_the_schematic_is_the_display_instance_and_says_so(self):
        display = read_json(os.path.join(SITE, "schematics", "display.json"))
        drawn = 0
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            sch = section(h, "schematic")
            with self.subTest(page=path):
                self.assertNotIn("not computed yet", sch)
                self.assertNotIn("stale", sch)
                if '<svg xmlns="http://www.w3.org/2000/svg" class="sch"' not in sch:
                    continue
                drawn += 1
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                params = display["tasks"][t]["params"]
                if params:
                    words = ", ".join(f"{k} = {params[k]}" for k in task["scoring"]["params"])
                    scored = ", ".join(f"{k} = {v}" for k, v in task["scoring"]["params"].items())
                    self.assertIn(f"Drawn at {words}, a display instance; scored at {scored}.", text_of(sch))
                    # the card holds the scored critical path and cells too: the drawing is the one pane that is not
                    # (said without "this tab": without the script there are no tabs)
                    self.assertIn("the critical path, the cells and every other number on this page are the scored "
                                  "netlist's", text_of(sch))
                    self.assertNotIn("this tab", text_of(sch))
                    self.assertIn(f"drawn at {words}", text_of(re.search(r'<p class="label pane-scale">(.*?)</p>',
                                                                         sch).group(1)))
                else:
                    self.assertIn("one fixed size", text_of(sch))
                self.assertEqual(h.count('class="sch"'), 1)
        self.assertGreaterEqual(drawn, 15)

    def test_the_critical_path_table_is_ppa_pys(self):
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            sha = rec["files"]["sv"]["sha256"] if rec else None
            if stem:
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                ref = next(r for r in task["references"] if posixpath.basename(r["sv"]) == stem + ".sv")
                with open(os.path.join(SVGOLF, "tasks", t, ref["sv"]), "rb") as fh:
                    sha = hashlib.sha256(fh.read()).hexdigest()
            data = read_json(os.path.join(SITE, "schematics", t, sha[:16] + ".json"))
            cp = section(h, "critical-path")
            rows = re.findall(r"<tr><td class=\"num\">(\d+)</td>", cp)
            with self.subTest(page=path):
                self.assertEqual(len(rows), len(data["scored"]["path"]))
                self.assertIn(f"{data['scored']['delay_ps_sky130']:,}".replace(",", " ") + " ps", text_of(cp))
                last = data["scored"]["path"][-1]
                self.assertIn(f"{last['arrival_ps']:,.1f}".replace(",", " "), text_of(cp))

    def test_the_critical_path_links_into_the_schematic(self):
        """Each cell of a critical path the page lists links to its cell in the drawing (`#sch-<instance>`, an id the
        page gives the cell's group): the scored table's instances when the drawing is the scored netlist (aes_sbox),
        else the display instance's path, listed under the table's lead. Every link resolves on the page."""
        linked = 0
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            sch, cp = section(h, "schematic"), section(h, "critical-path")
            if '<svg xmlns="http://www.w3.org/2000/svg" class="sch"' not in sch:
                continue
            sha = rec["files"]["sv"]["sha256"] if rec else self.ref_sha(t, stem)
            data = read_json(os.path.join(SITE, "schematics", t, sha[:16] + ".json"))
            disp, sc = data["display"], data["scored"]
            ids = set(re.findall(r'<g [^>]*id="sch-([^"]+)" data-inst="\1"', sch))
            hrefs = re.findall(r'<a class="sch-link" href="#sch-([^"]+)">', cp)
            with self.subTest(page=path):
                self.assertEqual(len(ids), disp["drawn_cells"])
                self.assertTrue(set(hrefs) <= ids, sorted(set(hrefs) - ids)[:3])
                if disp["params"] == sc["params"]:
                    want = [n["inst"] for n in sc["path"] if n.get("inst")]
                    self.assertNotIn('<ol class="chain">', cp)
                else:
                    want = [n["inst"] for n in disp["path"] if n.get("inst")]
                    chain = re.search(r'<ol class="chain">(.*?)</ol>', cp, re.S)
                    self.assertIsNotNone(chain)
                    end = disp["critical"]["output"]            # a clocked path ends at a flip-flop's D: `D:<net>`
                    self.assertIn(f"{end[2:]} flip-flop D" if end.startswith("D:") else end, text_of(chain.group(1)))
                self.assertEqual(hrefs, want)
                linked += 1
        self.assertGreaterEqual(linked, 15)

    def test_the_drawing_is_offered_on_its_own(self):
        """The schematic as a file of its own (the committed SVG, byte for byte), linked from the page: the browser's
        own zoom works there, with or without the script."""
        for t, path, rec, stem in self.detail_pages():
            sch = section(self.page(path), "schematic")
            if '<svg xmlns="http://www.w3.org/2000/svg" class="sch"' not in sch:
                continue
            sha = rec["files"]["sv"]["sha256"] if rec else self.ref_sha(t, stem)
            out = f"tasks/{t}/schematics/{sha[:16]}.svg"
            with self.subTest(page=path):
                self.assertIn(f'href="{posixpath.relpath(out, posixpath.dirname(path))}"', sch)
                with open(os.path.join(SITE, "schematics", t, sha[:16] + ".svg"), "rb") as fh:
                    self.assertEqual(self.files[out], fh.read())

    def test_a_drawing_comes_with_netlistsvgs_notice(self):
        """The drawings are derived from netlistsvg's default skin (MIT, NOTICE): every page that shows one names the
        licence and links the notice, site/schematics/LICENSE-netlistsvg.txt byte for byte, beside the drawings."""
        with open(os.path.join(SITE, "schematics", "LICENSE-netlistsvg.txt"), "rb") as fh:
            notice = fh.read()
        drawn = 0
        for t, path, rec, stem in self.detail_pages():
            sch = section(self.page(path), "schematic")
            if '<svg xmlns="http://www.w3.org/2000/svg" class="sch"' not in sch:
                continue
            drawn += 1
            out = f"tasks/{t}/schematics/LICENSE-netlistsvg.txt"
            with self.subTest(page=path):
                self.assertIn("MIT licence, Copyright (c) 2016 Neil Turley", text_of(sch))
                self.assertIn(f'href="{posixpath.relpath(out, posixpath.dirname(path))}"', sch)
                self.assertEqual(self.files[out], notice)
        self.assertGreater(drawn, 0)
        for f in self.files:
            if f.endswith(".svg") and "/schematics/" in f:
                self.assertIn(posixpath.join(posixpath.dirname(f), "LICENSE-netlistsvg.txt"), self.files, f)

    def ref_sha(self, t, stem):
        task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
        ref = next(r for r in task["references"] if posixpath.basename(r["sv"]) == stem + ".sv")
        with open(os.path.join(SVGOLF, "tasks", t, ref["sv"]), "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()

    def test_the_cells_add_up_to_the_ranked_area(self):
        for t, path, rec, stem in self.detail_pages():
            cells = section(self.page(path), "cells")
            m = re.search(r"<strong>total</strong></td><td class=\"num\"><strong>([\d\u202f]+)</strong></td>"
                          r"<td class=\"num\"></td><td class=\"num\"><strong>([\d.]+)</strong>", cells)
            with self.subTest(page=path):
                self.assertIsNotNone(m, "no total row")
                if rec is not None and isinstance(rec.get("ppa"), dict) and rec["ppa"].get("available"):
                    self.assertEqual(m.group(2), lb.fmt_um2(rec["ppa"]["area_e4um2_sky130"]))
                    self.assertEqual(int(m.group(1).replace("\u202f", "")), rec["ppa"]["cells_sky130"])
                self.assertNotIn("a stale cell list", cells)

    def test_a_licensed_design_shows_its_notices_and_licence_texts(self):
        lic_dir = os.path.join(SVGOLF, "tasks", "fdivp", "reference", "LICENSES")
        for t, path, rec, stem in self.detail_pages():
            if t != "fdivp":
                continue
            h = self.page(path)
            sv = (rec and rec["files"]["sv"]["name"]) or f"{stem}.sv"
            src = section(h, "sources")
            if "fdivp_srt" not in sv:
                self.assertNotIn('class="licence"', src)
                continue
            with self.subTest(page=path):
                self.assertIn("Apache-2.0 WITH SHL-2.1", text_of(src))
                self.assertIn("Copyright (C) 2021-26 Harvey Mudd College", text_of(src))
                for f in sorted(os.listdir(lic_dir)):
                    out = f"tasks/fdivp/reference/LICENSES/{f}"
                    self.assertIn(f'href="{posixpath.relpath(out, posixpath.dirname(path))}"', src)
                    with open(os.path.join(lic_dir, f), "rb") as fh:
                        self.assertEqual(self.files[out], fh.read())

    def test_reproduce_names_the_command_and_the_hashes(self):
        for t, path, rec, stem in self.detail_pages():
            rp = text_of(section(self.page(path), "reproduce"))
            with self.subTest(page=path):
                self.assertIn(f"score/ppa.py", rp)
                self.assertIn(f"--task tasks/{t}", rp)
                if rec is not None and isinstance(rec.get("ppa"), dict) and rec["ppa"].get("available"):
                    self.assertIn(rec["ppa"]["repair"]["netlist_sha256"], rp)
                    self.assertIn(rec["score"]["rtlil_sha256"], rp)
                    self.assertIn("leaderboard.py verify", rp)


if __name__ == "__main__":
    unittest.main()
