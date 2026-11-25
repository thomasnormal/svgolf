"""The detail pages of the site: one per record and one per proved reference without a record (PLAN4 3b step 3):
the page's head and the overview (Area, Performance and Score cards, with their beats/matches lines once there is a
field), then five tabs (decided 2026-11-16): "Source and proof" (the sources across the page, then the record's or
the reference's facts and the proof's), "Writeup", "Schematics" (the netlist card, whose own tabs are the schematic
of the display instance, the critical path, the cells and, on the routed course, the layout), "Charts" (the
area-time plot) and "Reproduce and verify" (the commands, then a record's checker and post-synthesis check). Built
once with --offline. (Before 2026-11-16 the same cards stood on one page: the code before the schematic, the record
and the proof in a second column, decided 2026-11-09.)

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)

No network, no Yosys, no Lean: the schematic data are the committed files of site/schematics/.
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


def element_from(page_html, start):
    """The element that starts at `start` in `page_html`, to its matching close tag (by nesting of the same tag)."""
    tag = re.match(r"<(\w+)", page_html[start:]).group(1)
    depth = 0
    for t in re.finditer(r"<(/?)" + tag + r"\b", page_html[start:]):
        depth += -1 if t.group(1) else 1
        if depth == 0:
            return page_html[start:start + page_html.index(">", start + t.end()) + 1 - start]
    return page_html[start:]


# the five tabs of a detail page (build.DETAIL_TABS, decided 2026-11-16): (pane id, label)
TABS = (("source", "Source and proof"), ("writeup", "Writeup"), ("schematics", "Schematics"), ("charts", "Charts"),
        ("reproduce", "Reproduce and verify"))


def tab_of(page_html, sid):
    """The id of the page's tab whose pane holds the element `sid` (None: above the tabs, or not on the page)."""
    for pid, _ in TABS:
        if f'id="{sid}"' in section(page_html, pid):
            return pid
    return None


class _Tree(html.parser.HTMLParser):
    """A page as a tree of dicts (tag, attrs, children, text): the site's HTML is well formed."""
    VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.root = {"tag": "#root", "attrs": {}, "children": [], "text": ""}
        self.stack = [self.root]

    def node(self, tag, attrs):
        n = {"tag": tag, "attrs": {k: "" if v is None else v for k, v in attrs}, "children": [], "text": ""}
        self.stack[-1]["children"].append(n)
        return n

    def handle_starttag(self, tag, attrs):
        n = self.node(tag, attrs)
        if tag not in self.VOID:
            self.stack.append(n)

    def handle_startendtag(self, tag, attrs):
        self.node(tag, attrs)

    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, 0, -1):
            if self.stack[i]["tag"] == tag:
                del self.stack[i:]
                return

    def handle_data(self, data):
        self.stack[-1]["text"] += data


def skeleton(page_html):
    """The skeleton of a page that site.js and charts.js act on, for tests/site/tabsjs_check.js: every element with an
    id, the tab bars and their panes, every link to a fragment (with its text), the course wrappers, the disclosures,
    and the schematic's box, tools and drawing; any other element is left out, its kept descendants moved up to the
    nearest kept ancestor. `ids`: every id kept."""
    keep_cls = {"tabs", "tabs-nav", "tabs-pane", "tabs-pane-title", "props", "props-head", "props-tabs", "sch-box",
                "sch-tools", "pdk-sky130", "pdk-asap7pnr", "hnote-btn", "hnote-body"}
    keep_attr = ("data-tabs", "data-schematic", "data-schematic-tools", "data-zoom", "data-crit", "data-find",
                 "data-find-count")
    attrs_kept = ("id", "class", "href", "hidden", "width", "height", "role", "tabindex", "data-inst", "aria-controls",
                  "aria-expanded", "type") + keep_attr
    t = _Tree()
    t.feed(page_html)
    ids = []

    def text(n):
        return n["text"] + "".join(text(c) for c in n["children"])

    def keep(n):
        a, cls = n["attrs"], set(n["attrs"].get("class", "").split())
        return ("id" in a or cls & keep_cls or any(k in a for k in keep_attr) or n["tag"] == "details"
                or (n["tag"] == "a" and a.get("href", "").startswith("#")) or (n["tag"] == "svg" and "sch" in cls))

    def walk(n):
        out = []
        for c in n["children"]:
            kids = walk(c)
            if not keep(c):
                out.extend(kids)
                continue
            a = {k: v for k, v in c["attrs"].items() if k in attrs_kept}
            if "id" in a:
                ids.append(a["id"])
            k = {"tag": c["tag"], "attrs": a, "children": kids}
            if c["tag"] == "a":
                k["text"] = norm(text(c)).strip()
            out.append(k)
        return out
    body = walk(t.root)
    return {"tag": "div", "attrs": {}, "children": body, "ids": ids}


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
        """Every proof of par's design is linked from its task page: par's from the leaderboard's par row, every one
        from the explorer's table ("Compare the designs"); since 2026-11-13 there is no Par card."""
        for t in self.listed:
            with self.subTest(task=t):
                task_html = self.page(f"tasks/{t}/index.html")
                self.assertNotIn('id="references"', task_html)
                refs = section(task_html, "explore")
                par_row = re.findall(r'<li class="par">(.*?)</li>', section(task_html, "leaderboard"), re.S)
                for _, path, rec, stem in self.detail_pages():
                    if not path.startswith(f"tasks/{t}/"):
                        continue
                    href = posixpath.relpath(path, f"tasks/{t}")
                    if stem is not None or (rec and rec["player"] == self.config["reference_player"]):
                        self.assertIn(f'href="{href}"', refs, path)
                self.assertTrue(par_row and any('href="' in r for r in par_row))
                for r in par_row:
                    self.assertRegex(r, r'<a href="(records|reference)/[^"]+\.html">')
                # the charts' reference marks open the same pages
                for m in re.finditer(r'<a href="([^"]+)" aria-label="[^"]*"><g class="mark[^"]*" data-kind="reference"',
                                     task_html):
                    self.assertTrue(m.group(1).startswith(("reference/", "records/")), m.group(1))

    def test_a_preview_has_no_detail_pages(self):
        """A preview ranks nothing: no record page, no reference page; its references are rows of the explorer's table
        (no Par card since 2026-11-13), its charts' marks link nowhere, and no page of the task says it is ranked."""
        if not self.previews:                       # none since matmul and the sorter rank (2026-11-08)
            self.skipTest("config.json lists no preview")
        for t in self.previews:
            with self.subTest(task=t):
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                pages = [p for p in self.files if p.startswith((f"tasks/{t}/records/", f"tasks/{t}/reference/"))
                         and p.endswith(".html")]
                self.assertEqual(pages, [])
                task_html = self.page(f"tasks/{t}/index.html")
                refs = section(task_html, "explore")
                for ref in shown_refs(task):
                    stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                    self.assertIn(f">{stem}<", refs)
                    self.assertNotIn(f'href="reference/{stem}.html"', task_html)
                self.assertFalse(re.search(r'<a href="[^"]+" aria-label="[^"]*"><g class="mark[^"]*" '
                                           r'data-kind="reference"', task_html))
                for path in (p for p in self.files if p.startswith(f"tasks/{t}/") and p.endswith(".html")):
                    self.assertNotIn("· ranked", text_of(self.page(path)), path)

    def test_every_detail_page_has_its_sections_in_order(self):
        """The order (decided 2026-11-09, in tabs since 2026-11-16): the head and the overview, then the tabs: the
        code, then the record's facts and its proof's (Source and proof); the writeup; the netlist (the schematic, the
        critical path, the cells: Schematics); the area-time plot (Charts); reproduce, then a record's checker and
        post-synthesis check (Reproduce and verify; since 2026-11-13, the owner's UI feedback item 4, "boring": at the
        bottom, a clocked record's per-point table last). Without the script, and printed, the panes stand in this
        order."""
        for t, path, rec, stem in self.detail_pages():
            order = ("dashboard", "source", "sources") + (("record", "proof") if rec else ("reference",))
            order += ("writeup", "schematics", "netlist", "schematic", "critical-path", "cells", "charts", "area-time",
                      "reproduce") + (("checker", "postsynth") if rec else ())
            with self.subTest(page=path):
                h = self.page(path)
                if "No ranked numbers to show" in text_of(section(h, "dashboard")):
                    order = tuple(o for o in order if o != "area-time")
                at = [h.find(f'id="{sid}"') for sid in order]
                self.assertTrue(all(a >= 0 for a in at), dict(zip(order, at)))
                self.assertEqual(at, sorted(at))
                self.assertLess(h.index('<header class="page-head">'), h.index('id="dashboard"'))
                self.assertIn('src="../../../charts.js"', h)
                self.assertNotRegex(h, r"(?<![\d\u202f])\b1 cells\b")       # "1 cell" (review 2026-11-09, N2)

    def test_every_detail_page_has_five_tabs(self):
        """Decided 2026-11-16 (the owner's request: "Tab 1: source code and proof, Tab 2: Writeup, Tab 3: Schematics,
        Tab 4: Plots/Charts, Tab 5: Reproduce and verify"): under the page's head and the overview, one tab bar of
        exactly five tabs in this order, named "Source and proof", "Writeup", "Schematics", "Charts", "Reproduce and
        verify", each a link to its pane (a `<section>` with the tab's id, the fragment that names the tab: `#writeup`),
        each pane under its title (an `<h2>`, for heading navigation and for a reader without the script). No tab is
        marked as chosen in the HTML (without the script the panes all stand there); site.js makes the tabs, the
        first chosen. The record's head (title, who made it, badges) and the overview (the scores, the board) are
        above the tabs, in no pane; nothing of the page is outside the head, the overview and the five panes."""
        for t, path, rec, stem in self.detail_pages():
            raw = self.files[path].decode("utf-8")
            with self.subTest(page=path):
                bars = re.findall(r'<div class="tabs tabs-page" data-tabs="page"><nav class="tabs-nav" '
                                  r'aria-label="([^"]+)">(.*?)</nav>', raw, re.S)
                self.assertEqual(len(bars), 1)
                label, nav = bars[0]
                self.assertEqual(label, "sections of this page")
                self.assertEqual(re.findall(r'<a href="#([^"]+)">([^<]+)</a>', nav), [(i, n) for i, n in TABS])
                self.assertNotIn("aria-selected", nav)
                self.assertNotIn('class="on"', nav)
                for pid, name in TABS:
                    self.assertIn(f'<section class="tabs-pane" id="{pid}"><h2 class="tabs-pane-title">{name}</h2>',
                                  raw)
                    self.assertEqual(raw.count(f'id="{pid}"'), 1, pid)          # no card keeps a tab's id
                main = raw[raw.index("<main"):raw.index("</main>")]
                start = main.index('<div class="tabs tabs-page"')
                before = main[:start]
                for part in ('<header class="page-head">', "<h1>", 'class="head-tags"', 'id="dashboard"') + \
                        (('class="head-sub"',) if rec else ('class="head-lead"',)):
                    self.assertIn(part, before)
                tabs = element_from(main, start)
                self.assertEqual(main[start + len(tabs):].strip(), "")         # the tabs end the page's main column
                self.assertEqual([pid for pid, _ in TABS if f'<section class="tabs-pane" id="{pid}">' in tabs],
                                 [pid for pid, _ in TABS])

    def test_each_card_is_in_its_tab(self):
        """The mapping of the page's cards to its five tabs (decided 2026-11-16; every card of the page before kept):
        Source and proof: the sources (the design file in a code box, the proof folded under it: in a column the code
        box showed 81 columns at 1280 px, review 2026-11-09 M1, so it spans the pane), then the record's facts and the
        proof's (a record's page) or the reference's facts, side by side where there is room; Writeup: the writeup;
        Schematics: the netlist card with its own tabs; Charts: the area-time plot; Reproduce and verify: the commands,
        then a record's checker card and post-synthesis check, folded (their facts behind closed disclosures; decided
        2026-11-13, the owner's UI feedback item 4, "boring": out of the way), side by side where there is room, a
        clocked record's per-point table across the pane, last."""
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            raw = self.files[path].decode("utf-8")
            with self.subTest(page=path):
                want = {"sources": "source", "netlist": "schematics", "schematic": "schematics",
                        "critical-path": "schematics", "cells": "schematics", "layout": "schematics",
                        "area-time": "charts", "dashboard": None}
                want.update({"record": "source", "proof": "source", "checker": "reproduce", "postsynth": "reproduce"}
                            if rec else {"reference": "source"})
                for sid, pid in want.items():
                    if sid == "area-time" and 'id="area-time"' not in raw:
                        continue
                    self.assertEqual(tab_of(raw, sid), pid, sid)
                self.assertNotIn('id="main-col"', raw)
                self.assertNotIn('id="side-col"', raw)
                src_pane = section(h, "source")
                facts = element_from(src_pane, src_pane.index('<div class="card-row">'))
                self.assertLess(src_pane.index('id="sources"'), src_pane.index(facts))
                if rec is None:
                    self.assertNotIn('id="checker"', h)
                    self.assertTrue(facts.startswith('<div class="card-row"><section class="card" id="reference">'))
                    continue
                self.assertTrue(facts.startswith('<div class="card-row"><section class="card" id="record">'))
                self.assertIn('<section class="card" id="proof">', facts)
                clocked = isinstance(rec["postsynth"].get("points"), list)
                rp = section(h, "reproduce")
                row = element_from(rp, rp.index('<div class="card-row">'))
                self.assertLess(rp.index('<h2 class="card-title">Reproduce and verify</h2>'), rp.index(row))
                self.assertTrue(row.startswith('<div class="card-row"><section class="card" id="checker">'))
                self.assertEqual('id="postsynth"' in row, not clocked)       # a clocked table needs the width
                if clocked:
                    self.assertGreater(rp.index('id="postsynth"'), rp.index(row) + len(row) - 1)
                for sid in ("checker", "postsynth"):
                    card = section(h, sid)
                    self.assertNotIn("<details open", card)                     # folded: closed disclosures
                    if sid == "checker" or not clocked:
                        self.assertNotIn("<dl", card.split("<details", 1)[0])   # no fact list outside a fold
                src = section(h, "sources")
                self.assertLess(src.index("<pre"), src.index("<details"))        # the design file, then the proof
                # the box's download link downloads, under the name the box's head shows (L8)
                name = rec["files"]["sv"]["name"] if rec else f"{stem}.sv"
                self.assertRegex(src, r'<a class="codebox-dl" href="[^"]+\.sv" download="' + re.escape(name) + '">')
                self.assertNotIn('id="diff"', h)          # no diff against an earlier record (decided 2026-11-13)
                self.assertIn('<span class="codebox-name">' + html.escape(
                    rec["files"]["sv"]["name"] if rec else f"{stem}.sv") + "</span>", src)

    def test_the_netlist_card_has_its_tabs(self):
        """The schematic, the critical path and the cells are three tabs of one card (site.js; without the script,
        panes under their titles): each pane a section with the id the page's links use. The overview links its cells
        and critical-path numbers to their tabs. A fourth tab, Layout, is the routed course's alone (decided
        2026-11-13, the owner's UI feedback items 1 and 10): its tab and its pane carry `pdk-asap7pnr`, so that on
        sky130 (and without JavaScript) no ASAP7 layout is anywhere on the page."""
        tasks = {t.name: t for t in self.tasks()}
        for t, path, rec, stem in self.detail_pages():
            h = self.page(path)
            card = section(self.files[path].decode("utf-8"), "netlist")      # both courses' tabs
            with self.subTest(page=path):
                nav = re.search(r'<nav class="tabs-nav"[^>]*>(.*?)</nav>', card, re.S)
                self.assertIsNotNone(nav)
                self.assertEqual(re.findall(r'<a href="#([^"]+)"', nav.group(1)),
                                 ["schematic", "critical-path", "cells", "layout"])
                self.assertEqual(text_of(nav.group(1)), "SchematicCritical pathCellsLayout")
                self.assertIn('<a href="#layout" class="pdk-asap7pnr">Layout</a>', nav.group(1))
                for sid in ("schematic", "critical-path", "cells"):
                    self.assertIn(f'<section class="tabs-pane" id="{sid}">', card)
                self.assertIn('<section class="tabs-pane pdk-asap7pnr" id="layout">', card)
                sky = section(self.page(path, "sky130"), "netlist")
                self.assertNotIn('href="#layout"', sky)
                self.assertNotIn('class="layout-fig', sky)
                self.assertNotIn("/layouts/", self.page(path, "sky130"))
                self.assertIn('href="#layout"', section(self.page(path, "asap7pnr"), "netlist"))
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
                for label in ("Area", "Performance · time", "Score · area × time", "vs par"):
                    self.assertIn(label, dash)
                # the place on the board and on the plot's front: the Charts tab's comparison (on the Score card until
                # 2026-11-16, the owner's item 3)
                compare = text_of(section(self.page(path), "compare"))
                self.assertIn("board", compare)
                self.assertNotIn("<dt>board</dt>", section(self.page(path), "dashboard"))
                # "on this page" and "Pareto" are rows only when the plot has other designs; alone, the note says so
                # once (each card said "the only design with sky130 numbers")
                alone = len(build.plotted(tasks[t])) == 1
                self.assertNotIn("the only design with sky130 numbers", dash)
                self.assertEqual(dash.count("This design is the only one with sky130 numbers on this page"), int(alone))
                if not alone:
                    self.assertIn("on this page", dash)
                    self.assertIn("Pareto", compare)
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
        """A record page's heading (decided 2026-11-13, the owner's UI feedback item 6): the record's title, its
        writeup's (leaderboard/writeups/<hash>.html, line 1) or else its design file's stem; under it who made the record,
        on which task, and when (decided 2026-11-11): "{player} on {task} · {date}" ("{stem} on {task} · reference"
        for a proved reference's record), its hash a chip of the tag row; the browser's <title> "{title} · {player} on
        {task} · record {hash, first 12}", unique per page. No score in either: the score differs by course, and the
        title cannot switch with the view."""
        titles = []
        for t, path, rec, stem in self.detail_pages():
            if rec is None:
                continue
            raw = self.files[path].decode("utf-8")
            h1 = text_of(re.search(r"<h1\b[^>]*>(.*?)</h1>", raw, re.S).group(1)).strip()
            sub = text_of(re.search(r'<p class="head-sub">(.*?)</p>', raw, re.S).group(1)).strip()
            title = html.unescape(re.search(r"<title>(.*?)</title>", raw, re.S).group(1))
            titles.append(title)
            wpath = os.path.join(SVGOLF, "leaderboard", "writeups", rec["record_hash"] + ".html")
            if os.path.isfile(wpath):
                with open(wpath, encoding="utf-8") as fh:
                    mine_title = lb.writeup_title(fh.read())
            else:
                mine_title = posixpath.splitext(rec["files"]["sv"]["name"])[0]
            with self.subTest(page=path):
                self.assertEqual(h1, html.unescape(html.escape(mine_title)))
                self.assertNotIn("µm²·ns", h1 + sub + title)
                self.assertNotIn("µm", h1 + sub + title)
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
                    self.assertEqual(sub, f"{who} on {on} · " + ("reference" if mine else rec["submitted_at"][:10]))
                else:
                    who = rec["player"]
                    self.assertEqual(sub, f"{rec['player']} on {on} · {rec['submitted_at'][:10]}")
                self.assertEqual(title, f"{mine_title} · {who} on {on} · record {h12} | svGolf")
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
                for part in ('<h3 class="label"', 'class="big"', 'class="sub"', 'class="mfield"', 'class="mbody"'):
                    self.assertEqual(dash.count(part), 3, part)
                for big in re.findall(r'<p class="big">(.*?)</p>', dash):
                    self.assertNotIn(" ", re.sub(r'<span class="g"> </span>', "", big))
                self.assertNotIn("<code>", "".join(re.findall(r'<dt>vs par</dt><dd>(.*?)</dd>', dash)))
                for v in re.findall(r'<dt>vs par</dt><dd>(.*?)</dd>', dash):
                    if "is par" not in v and "no par" not in v:
                        self.assertRegex(v, r'<span class="mpar"><a href="[^"#][^"]*">[^<]+</a> · ')
                note = dash[dash.index('<div class="dash-note">'):]
                self.assertIn(f'<details class="reveal dash-more"><summary>{build.DASH_MORE}</summary>', note)
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

    def test_the_cards_show_the_number_vs_par_and_on_this_page(self):
        """Decided 2026-11-16 (the owner's item 3, "Trim the overview cards"): a card keeps its number with its unit, the
        line under it, the field's line, "vs par" and "on this page"; nothing else. Its secondary numbers (cells,
        flops, repair, GE, the cells-only columns, Fmax-equivalent, the critical path's cells, unit depth, the
        routed run) and the time's measurement sentence are the overview's fold's, one click away, a column per
        card, the cells and critical-path links with them; the place on the board and on the plot's front are the
        Charts tab's (test_charts_compare_with_par_and_the_neighbours)."""
        checked = 0
        for t, path, rec, stem in self.detail_pages():
            for pdk in ("sky130", build.COURSE2):
                dash = section(self.page(path, pdk), "dashboard")
                if "No ranked numbers to show" in text_of(dash):
                    continue
                checked += 1
                with self.subTest(page=path, pdk=pdk):
                    cards = re.findall(r'<section class="mcard[^"]*".*?</section>', dash, re.S)
                    self.assertEqual(len(cards), 3)
                    for card in cards:
                        self.assertNotIn("mfacts", card)
                        rows = re.findall(r"<dt>([^<]+)</dt>", card)
                        self.assertEqual(rows[0], "vs par")
                        self.assertTrue(set(rows) <= {"vs par", "on this page"}, rows)
                    fold = re.search(r'<details class="reveal dash-more"><summary>[^<]*</summary>(.*?)</details>',
                                     dash, re.S)
                    self.assertIsNotNone(fold)
                    facts = fold.group(1).split('<div class="dash-facts">', 1)[1]
                    for row in ("cells", "flops", "GE", "Fmax-eq.", "unit depth"):
                        self.assertIn(f"<dt>{row}</dt>", facts)
                    if pdk == build.COURSE2:
                        for row in ("cells only (A0′)", "routed run"):
                            self.assertIn(f"<dt>{html.escape(row)}</dt>", facts)
                        # decided 2026-11-17: no "wire cost" (negative on some designs, never analysed); the
                        # cells-only score is a row of its own, beside the routed one
                        self.assertNotIn("wire cost", facts)
                        self.assertEqual(facts.count("<dt>cells only (A0′)</dt>"), 3)
                    else:
                        self.assertIn('<a href="#cells">', facts)
                        if rec is not None and (rec.get("ppa") or {}).get("repair"):
                            self.assertIn("<dt>repair</dt>", facts)
                    # the time's measurement sentence is the fold's; the card says what the time is in a few words
                    time_card = cards[1]
                    sub = text_of(re.search(r'<p class="sub">(.*?)</p>', time_card, re.S).group(1))
                    self.assertLessEqual(len(sub), 40, sub)
                    self.assertRegex(text_of(facts), r"(the delay: the latest output arrival|the period is|the "
                                                     r"register-to-register period|the period, one decision per cycle:)")
        self.assertGreaterEqual(checked, 40)

    def test_the_overview_fold_stands_open_without_the_script_and_printed(self):
        """The overview's fold holds numbers the cards showed until 2026-11-16 (the owner's item 3), which a reader
        without JavaScript and a printed page showed: without the script (no <html data-pdk>) and printed it stands
        open, its summary a plain line (style.css, ::details-content; for printing site.js also opens it and closes it
        again after). Checked in the browser by the round's headless check (no JavaScript, and a printed PDF)."""
        css = open(os.path.join(SITE, "style.css"), encoding="utf-8").read()
        self.assertIn("html:not([data-pdk]) details.dash-more::details-content { content-visibility: visible; }", css)
        self.assertIn("html:not([data-pdk]) details.dash-more > summary { pointer-events: none; }", css)
        self.assertRegex(css, r"@media print \{\n  details\.dash-more::details-content \{ content-visibility: visible; \}"
                              r"\n\}")
        js = open(os.path.join(SITE, "site.js"), encoding="utf-8").read()
        self.assertIn('window.addEventListener("beforeprint"', js)
        self.assertIn('document.querySelectorAll("details.dash-more")', js)

    def test_a_phone_shows_the_three_numbers_in_one_row(self):
        """Decided 2026-11-16 (the owner's item 1, "Compact the overview on phones": the three cards took about two
        screens before the tabs): on a phone the three cards stand in one row, each its label's short words, its
        number with its unit and "vs par"; the cards' other lines and the note under them open with the overview's
        fold, one tap (a <details>: the browser's own disclosure, keyboard and touch, no script). The HTML is the wide
        screen's; style.css makes the row, only on screen, only with the script on (<html data-pdk>, which pdk.js
        sets before the page is drawn) and only where :has() is known, so that without JavaScript and printed every
        line is shown. Measured in the browser (the round's headless check): the tab bar starts 0.8 screens down at
        390 px on the sorter's page, from 1.7."""
        css = open(os.path.join(SITE, "style.css"), encoding="utf-8").read()
        block = css[css.index("@supports selector(:has(a)) {"):]
        block = block[:block.index("\n}\n") + 3]
        self.assertIn("@media screen and (max-width: 42rem)", block)
        rules = [r for r in re.findall(r"([^{}]+)\{([^{}]*)\}", block) if "#dashboard" in r[0]]
        self.assertTrue(rules)
        def parts(sel):             # a selector list's selectors (commas inside :is() and :has() kept)
            out, depth, cur = [], 0, ""
            for ch in sel:
                depth += (ch == "(") - (ch == ")")
                if ch == "," and depth == 0:
                    out.append(cur)
                    cur = ""
                else:
                    cur += ch
            return out + [cur]
        for sel, _ in rules:
            for part in parts(sel):
                self.assertTrue(part.strip().startswith(
                    "html[data-pdk] #dashboard .pdk:not(:has(details.dash-more[open]))"), part)
        hidden = " ".join(sel for sel, body in rules if "display: none" in body)
        for part in (".lab-more", ".sub", ".mfield", ".mpar", "dl.mrows > :is(dt, dd)", "> .dash-note > .fine"):
            self.assertIn(part, hidden)
        self.assertIn("repeat(3, minmax(0, 1fr))", block)
        self.assertNotIn("@media print", block)
        for t, path, rec, stem in self.detail_pages():
            raw = self.files[path].decode("utf-8")
            dash = section(raw, "dashboard")
            if 'class="dash"' not in dash:
                continue
            with self.subTest(page=path):
                for course in re.findall(r'<div class="pdk pdk-[^"]+"><div class="dash">(.*?)</details></div></div>',
                                         dash, re.S):
                    labels = [text_of(x) for x in re.findall(r'<h3 class="label"[^>]*>(.*?)</h3>', course)]
                    self.assertEqual(labels, ["Area", "Performance · time", "Score · area × time"])
                    short = [text_of(re.sub(r'<span class="lab-more">.*?</span>', "", x))
                             for x in re.findall(r'<h3 class="label"[^>]*>(.*?)</h3>', course)]
                    self.assertEqual(short, ["Area", "time", "Score"])
                    # the first row of each card is "vs par", the one the row keeps
                    for card in re.findall(r'<section class="mcard.*?</section>', course, re.S):
                        self.assertTrue(re.search(r'<dl class="mrows"><dt>vs par</dt>', card), card[:200])
                    self.assertIn(f'<details class="reveal dash-more"><summary>{build.DASH_MORE}</summary>', course)

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

    def subject_of(self, task, rec, stem):
        """The design a detail page is about, as its task's designs of the course in view hold it (None: no ranked
        numbers there): a player's record by its hash, the reference player's record and a reference page by the
        reference's stem."""
        if rec is not None and rec["player"] != self.config["reference_player"]:
            return next((d for d in task.designs if d["id"] == rec["record_hash"]), None)
        if stem is None:
            ref = task.ref_of_record.get(rec["record_hash"])
            stem = ref["stem"] if ref else None
        d = next((d for d in task.designs if d["kind"] == "reference" and d["stem"] == stem), None)
        return d if d is not None and "area_um2" in d["m"] and "time_ps" in d["m"] else None

    def test_charts_compare_with_par_and_the_neighbours(self):
        """Decided 2026-11-16 (the owner's item 4, "Put the comparison in Charts"): the Charts tab opens with a small
        table of this design against par and its neighbours on the board of the course in view: the ranked records just
        better and just worse by score (and any of equal score), in the board's order, each with its area, time and
        score, and this design's score against each as the cards' "vs par" says it (par's row says exactly the Score
        card's vs par). Each course's table is its own (the selector picks it); the board's and the plot's numbers, no
        new measurement."""
        tasks = {t.name: t for t in self.tasks()}
        checked = 0
        for t, path, rec, stem in self.detail_pages():
            for pdk in ("sky130", build.COURSE2):
                h = self.page(path, pdk)
                charts = section(h, "charts")
                with self.subTest(page=path, pdk=pdk), tasks[t].view(pdk):
                    task = tasks[t]
                    d = self.subject_of(task, rec, stem)
                    if pdk == build.COURSE2 and rec is not None and self.pnr_entry(
                            t, rec["files"]["sv"]["sha256"]) is None:
                        d = None
                    if d is None or "No ranked numbers to show" in text_of(section(h, "dashboard")):
                        self.assertNotIn('id="compare', charts)
                        continue
                    cmp_ = section(h, "compare")
                    self.assertTrue(cmp_, "no comparison")
                    self.assertLess(charts.index('id="compare'), charts.index('id="area-time'))
                    score = {x["id"]: build.standing.score(build.st_point(x, pdk)) for x in task.designs
                             if "area_um2" in x["m"] and "time_ps" in x["m"]}
                    me = score[d["id"]]
                    recs = [x for x in task.designs if x["kind"] == "record" and x["id"] != d["id"] and x["id"] in score]
                    better = sorted((x for x in recs if score[x["id"]] < me), key=lambda x: score[x["id"]])[-1:]
                    worse = sorted((x for x in recs if score[x["id"]] > me), key=lambda x: score[x["id"]])[:1]
                    tied = [x for x in recs if score[x["id"]] == me]
                    par = next((x for x in task.designs if x["par"] and x["id"] in score), None)
                    want = {x["id"] for x in [d] + better + worse + tied + ([par] if par else [])}
                    rows = [r for r in re.findall(r"<tr( class=\"is-subject\")?>(.*?)</tr>", cmp_, re.S) if "<td" in r[1]]
                    if len(want) == 1:                                          # no par score, no other record
                        self.assertIn("Nothing to compare with on this course", text_of(cmp_))
                        self.assertEqual(rows, [])
                        checked += 1
                        continue
                    self.assertEqual(len(rows), len(want), [text_of(r[1])[:40] for r in rows])
                    self.assertEqual(sum(1 for r in rows if r[0]), 1)              # this design's row, marked
                    for x in better + worse + tied:
                        self.assertIn(f'{x["id"]}.html"', cmp_)
                    if par is not None and par["id"] != d["id"]:
                        (prow,) = [r[1] for r in rows if "· par<" in r[1] or "· par</span>" in r[1]]
                        vs = text_of(re.findall(r"<td[^>]*>(.*?)</td>", prow)[-1]).strip()
                        card = re.search(r'<dt>vs par</dt><dd>(?:<span class="good">)?<strong>([^<]+)</strong> (\w+)'
                                         r'(?:</span>)?<span',
                                         section(h, "dashboard").split('id="h-score', 1)[1])
                        self.assertEqual(vs, f"{card.group(1)} {card.group(2)}")
                    checked += 1
        self.assertGreaterEqual(checked, 30)

    def test_charts_show_both_courses(self):
        """Decided 2026-11-16 (the owner's item 4): where the design has numbers on both courses, the Charts tab draws
        the area-time plot of each, the course in view first (style.css orders them; in the HTML, and so without the
        script and printed, sky130 first), each under its course's name, the other one's said to be the other course;
        every drawing's y-axis title says "lower is better". With numbers on one course only, that course's plot alone,
        as before."""
        both = 0
        for t, path, rec, stem in self.detail_pages():
            raw = self.files[path].decode("utf-8")
            box = section(raw, "area-time")
            if not box:
                continue
            with self.subTest(page=path):
                charts = re.findall(r'<svg[^>]*class="chart[^"]*".*?</svg>', box, re.S)
                self.assertTrue(charts)
                for svg in charts:
                    self.assertIn("lower is better", svg)
                if 'class="at-courses"' not in box:
                    continue
                both += 1
                sky = box.index('<div class="at-course at-sky130">')
                a7 = box.index(f'<div class="at-course at-{build.COURSE2}">')
                self.assertLess(sky, a7)
                for pdk, other in (("sky130", build.COURSE2), (build.COURSE2, "sky130")):
                    v = section(self.page(path, pdk), "area-time")
                    heads = [text_of(x) for x in re.findall(r'<h3 class="at-head">(.*?)</h3>', v, re.S)]
                    self.assertEqual(heads, ["sky130" + (" · the other course" if pdk != "sky130" else ""),
                                             "ASAP7 · placed and routed" + (" · the other course" if pdk == "sky130"
                                                                            else "")])
                    self.assertEqual(len(re.findall(r'<div class="chart-variant" [^>]*data-view="fit" '
                                                    r'data-size="wide"', v)) >= 2, True)
        self.assertGreaterEqual(both, 20)

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
                    # one line (decided 2026-11-16, the owner's item 6: it was five on a phone): the two sizes, always
                    # shown; what a display instance is, a note behind its button (shown in its place without the
                    # script and printed: style.css)
                    lead = re.search(r'<p class="sch-lead sch-scale"><span class="sch-line">(.*?)</span> '
                                     r'<button type="button" class="hnote-btn" aria-expanded="false" '
                                     r'aria-controls="schematic-note">why\?</button> '
                                     r'<span class="hnote-body" id="schematic-note">(.*?)</span></p>', sch, re.S)
                    self.assertIsNotNone(lead, sch[:400])
                    self.assertEqual(text_of(lead.group(1)), f"Drawn at {words}; scored at {scored}.")
                    self.assertTrue(text_of(lead.group(2)).startswith("This is a display instance. Only this drawing"))
                    self.assertEqual(h.count('id="schematic-note"'), 1)
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

    def test_the_display_instance_note_hides_only_with_the_script(self):
        """The display-instance note (decided 2026-11-16, the owner's item 6) is a hover note only on screen with the
        script on (<html data-pdk>): there style.css hides it until its button is hovered, focused or clicked (site.js,
        tabsjs_check.js), and shows the button; without the script and printed the button is not shown and the note
        stands in its place, after the line, as a sentence (the headless check's no-JavaScript and print runs)."""
        css = open(os.path.join(SITE, "style.css"), encoding="utf-8").read()
        self.assertRegex(css, r"\n\.hnote-btn \{ display: none; \}")
        for m in re.finditer(r"([^{}]+)\{([^{}]*visibility: hidden[^{}]*)\}", css):
            if "hnote" not in m.group(1):
                continue
            self.assertTrue(all(p.strip().startswith("html[data-pdk] ") for p in m.group(1).split(",")), m.group(1))
            before = css[:m.start()]
            self.assertGreater(before.rfind("@media screen"), before.rfind("}\n}\n"))      # inside @media screen
        printed = css[css.index("@media print {"):]
        self.assertNotIn("hnote", printed[:printed.index("\n}\n")])

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

    def pnr_entry(self, t, sha):
        """The BOUND routed entry of a design file (leaderboard.py's rule, from the files), or None."""
        status, _why, e = lb.asap7pnr_status(lb.load_asap7pnr(t), lb.load_asap7(t), sha,
                                             task=lb.load_task(os.path.join(SVGOLF, "tasks"), t),
                                             pins=lb.asap7pnr_identity())
        return e if status == "bound" else None

    def test_the_layout_picture_is_the_scored_runs_in_the_layout_tab(self):
        """Decided 2026-11-12 ("show the generated images in the schematic section of each submission"), and 2026-11-13
        (the owner's UI feedback items 1 and 10: a tab of its own beside the schematic, on the routed course only):
        every record page and par's page shows, in the netlist card's Layout tab on the routed course, the layout of
        its own design's scored run when it has a bound routed result: the 640 px thumbnail (width and height given,
        lazy), the full picture by srcset and linked at full size, both the committed files byte for byte and the
        sha256 its entry records, its alt text and its caption; without one, "No layout yet: place and route pending",
        never another design's picture. The sky130 view shows none."""
        seen = {"shown": 0, "none": 0}
        for t, path, rec, stem in self.detail_pages():
            sha = rec["files"]["sv"]["sha256"] if rec else self.ref_sha(t, stem)
            e = self.pnr_entry(t, sha)
            raw = self.files[path].decode("utf-8")
            pane = section(self.page(path, "asap7pnr"), "layout")
            with self.subTest(page=path):
                self.assertNotIn('class="layout-fig', self.page(path, "sky130"))
                self.assertNotIn('class="layout-fig', section(raw, "schematic"))
                figs = re.findall(r'<figure class="layout-fig[^"]*"[^>]*>(.*?)</figure>', pane, re.S)
                self.assertEqual(len(figs), 1)
                self.assertEqual(raw.count('class="layout-fig'), 1)
                self.assertIn("ASAP7 placed and routed", text_of(pane))
                if e is None:
                    seen["none"] += 1
                    self.assertIn("No layout yet: place and route pending.", text_of(figs[0]))
                    self.assertNotIn("<img", figs[0])
                    continue
                seen["shown"] += 1
                L = e["layout"]
                full, thumb = f"tasks/{t}/layouts/{sha[:16]}.webp", f"tasks/{t}/layouts/{sha[:16]}.thumb.webp"
                rf, rt = (posixpath.relpath(x, posixpath.dirname(path)) for x in (full, thumb))
                img = re.search(r"<img ([^>]*)>", figs[0]).group(1)
                self.assertIn(f'src="{rt}"', img)
                self.assertIn(f'srcset="{rt} {L["thumb_px"][0]}w, {rf} {L["image_px"][0]}w"', img)
                self.assertIn(f'width="{L["thumb_px"][0]}" height="{L["thumb_px"][1]}"', img)
                self.assertIn('loading="lazy"', img)
                name = f"record {rec['record_hash'][:12]}" if rec and rec["player"] != self.config["reference_player"] \
                    else None
                self.assertRegex(img, r'alt="Placed and routed layout of [^"]+ on ASAP7"')
                if name:
                    self.assertIn(f'alt="Placed and routed layout of {name} on ASAP7"', img)
                self.assertIn(f'<a class="layout-link" href="{rf}">', figs[0])
                self.assertIn(html.escape(L["caption"], quote=False), figs[0])
                self.assertIn(f"Full size ({L['image_px'][0]} × {L['image_px'][1]} px", text_of(figs[0]))
                for out, key in ((full, "image"), (thumb, "thumb")):
                    with open(os.path.join(SVGOLF, *L[key].split("/")), "rb") as fh:
                        blob = fh.read()
                    self.assertEqual(self.files[out], blob)
                    self.assertEqual(hashlib.sha256(blob).hexdigest(), L[f"{key}_sha256"])
                    self.assertEqual(list(lb.webp_size(blob)), L[f"{key}_px"])
        # every design is routed since 2026-11-13: a page without a bound entry ("No layout yet") is planted in
        # test_pdk.PdkTest.test_a_design_not_routed_yet_shows_no_routed_number
        self.assertTrue(seen["shown"], seen)
        # every picture the site offers is one a page shows (no stray file), and each is a design's own
        offered = sorted(p for p in self.files if "/layouts/" in p)
        self.assertTrue(offered)
        for p in offered:
            t, name = p.split("/")[1], p.rsplit("/", 1)[1]
            self.assertTrue(any(name.split(".")[0] == (r["files"]["sv"]["sha256"][:16]) for r in self.recs
                                if r["task"] == t) or any(name.split(".")[0] == self.ref_sha(t, st)[:16]
                                                          for tt, _, rr, st in self.detail_pages() if tt == t and st),
                            p)

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
                text = build.read_text(f"svgolf/leaderboard/data/fdivp/{rec['record_hash']}.sv" if rec else
                                       f"svgolf/tasks/fdivp/reference/{stem}.sv")
                if not build.licence_ids(text):
                    self.assertNotIn('class="licence"', src)
                    continue
                # a player's design built on fdivp_srt.sv that keeps its notice (casper-hansen's 0f04df325a62, since
                # 2026-11-25): its card claims the notice only, and the design file shown holds it
                with self.subTest(page=path):
                    self.assertIn("Adapted from licensed code (Apache-2.0 WITH SHL-2.1): its licence notice is in the "
                                  "design file, shown in full below.", norm(text_of(src)))
                    self.assertIn("Copyright (C) 2021-26 Harvey Mudd College", text_of(src))
                continue
            with self.subTest(page=path):
                self.assertIn("Apache-2.0 WITH SHL-2.1", text_of(src))
                self.assertIn("Copyright (C) 2021-26 Harvey Mudd College", text_of(src))
                for f in sorted(os.listdir(lic_dir)):
                    out = f"tasks/fdivp/reference/LICENSES/{f}"
                    self.assertIn(f'href="{posixpath.relpath(out, posixpath.dirname(path))}"', src)
                    with open(os.path.join(lic_dir, f), "rb") as fh:
                        self.assertEqual(self.files[out], fh.read())

    def test_an_empty_tab_says_so_in_one_line(self):
        """Every tab is kept on every detail page (decided 2026-11-16: kept, never hidden): a tab with nothing to show
        says so in one plain line, in the site's empty box. A reference's Writeup: a writeup belongs to a record. Charts,
        for a design with no ranked numbers on the course shown (the overview says why)."""
        for t, path, rec, stem in self.detail_pages():
            for pdk in ("sky130", "asap7pnr"):
                h = self.page(path, pdk)
                with self.subTest(page=path, pdk=pdk):
                    w = section(h, "writeup")
                    if rec is None:
                        self.assertEqual(w + ">", '<section class="tabs-pane" id="writeup"><h2 class="tabs-pane-title">'
                                            f'Writeup</h2><p class="empty">{html.escape(build.NO_WRITEUP_REFERENCE)}</p>'
                                            "</section>")
                    else:
                        self.assertTrue('<section class="card writeup">' in w or 'class="empty writeup-none"' in w)
                    charts = section(h, "charts")
                    if 'id="area-time' not in charts:
                        self.assertIn(f'<p class="empty">{html.escape(build.NO_CHART)}</p>', charts)
                        self.assertIn("No ranked numbers to show", text_of(section(h, "dashboard")))
                    else:
                        self.assertNotIn(build.NO_CHART, charts)

    def test_a_record_without_a_writeup_keeps_its_tab(self):
        """A record without a writeup (every record has one today: a writeup is kept beside the record, never in it,
        and anyone may add one later) keeps its Writeup tab, which says so in one line and links how to add one."""
        site = build.Site(build.load_config())
        refusals = json.loads(site.doc_text(site.config["refusals_json"]))
        site.stages = [s["id"] for s in refusals["svgolf"]["stages"]]
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            tasks = build.collect(site, True)
        t = next(t for t in tasks if t.name == "add")
        rec = next(r for r in t.records if r["player"] != self.config["reference_player"])
        site.writeups.pop(rec["record_hash"], None)
        build.record_page(site, t, rec, build.load_ge_tables())
        h = site.files[f"tasks/add/records/{rec['record_hash']}.html"].decode("utf-8")
        self.assertEqual(section(h, "writeup") + ">",                  # (section() stops before the last ">")
                         '<section class="tabs-pane" id="writeup"><h2 class="tabs-pane-title">Writeup</h2>'
                         f'<p class="empty writeup-none">{html.escape(build.WRITEUP_PROMPT)} '
                         '<a href="../../../rules.html#writeups">How to add a writeup</a>.</p></section>')
        self.assertEqual([pid for pid, _ in TABS if f'<section class="tabs-pane" id="{pid}">' in h], [p for p, _ in TABS])
        self.assertEqual(text_of(re.search(r"<h1\b[^>]*>(.*?)</h1>", h, re.S).group(1)),
                         posixpath.splitext(rec["files"]["sv"]["name"])[0])          # the file's stem as the title

    def test_the_tab_script(self):
        """site.js's tabs and charts.js's schematic under node (tests/site/tabsjs_check.js, with the skeleton of two
        real record pages: the sorter's 3b1ec4b16 (61bf6f8d1 until its re-make on 2026-11-16), the owner's example,
        clocked, and a combinational record with a drawing and critical-path links; skipped without node): the ARIA
        wiring and the roving tabindex, a click a new history entry, the keys, a fragment on load or by a link opening
        every tab around its target (the netlist card's inside the Schematics tab), Back and Forward, and the drawing
        in a hidden tab fitted when its tab is first shown (decided 2026-11-16: a chart or drawing measured in a hidden
        pane would get no width)."""
        node = shutil.which("node")
        if not node:
            self.skipTest("node is not installed")
        drawn = [path for _, path, rec, _ in self.detail_pages() if rec is not None and 'class="sch-link"' in
                 self.files[path].decode("utf-8")]
        sorter = [p for p in drawn if p.startswith("tasks/sorter/records/3b1ec4b16")] or \
            [p for p in drawn if p.startswith("tasks/sorter/")]
        comb = [p for p in drawn if p.startswith("tasks/add/")] or [p for p in drawn if "/sorter/" not in p]
        self.assertTrue(sorter and comb)
        for path in (sorter[0], comb[0]):
            with self.subTest(page=path):
                sk = os.path.join(self.tmp.name, "skeleton.json")
                with open(sk, "w", encoding="utf-8") as fh:
                    json.dump(skeleton(self.files[path].decode("utf-8")), fh)
                proc = subprocess.run([node, os.path.join(HERE, "tabsjs_check.js"), os.path.join(SITE, "site.js"),
                                       os.path.join(SITE, "charts.js"), sk], capture_output=True, text=True, timeout=120)
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                self.assertIn("all ok", proc.stdout)

    def test_source_and_proof_opens_with_what_is_proved(self):
        """Decided 2026-11-16 (the owner's item 5, "Give the proof its own summary line"): the Source and proof tab opens
        with one line, generated, never written per record: what is proved (the task's statement summary, its public
        one-line summary content/tasks/<task>.json `subtitle`, linking the statement on the task page), for which
        parameters (task.json's ranges, every condition) and how long the check took (the record's own
        `proof.build_seconds`; a reference without a record: the cold runs of its proof score/time_limits.json keeps,
        and without them nothing of time). A record checked under another statement says so instead."""
        limits = read_json(os.path.join(SVGOLF, "score", "time_limits.json"))["tasks"]
        for t, path, rec, stem in self.detail_pages():
            raw = self.files[path].decode("utf-8")
            pane = section(raw, "source")
            task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
            sub = read_json(os.path.join(SITE, "content", "tasks", f"{t}.json")).get("subtitle", "")
            with self.subTest(page=path):
                first = re.match(r'<section class="tabs-pane" id="source"><h2 class="tabs-pane-title">Source and proof'
                                 r'</h2><p class="proof-line">(.*?)</p>', pane, re.S)
                self.assertIsNotNone(first, pane[:300])
                line = text_of(first.group(1))
                self.assertIn('href="../index.html#spec"', first.group(1))
                if rec is not None and lb.statement_mismatch(rec, lb.current_statement(task)):
                    self.assertIn("against another version of the task's statement", line)
                    continue
                self.assertTrue(line.startswith("proved the task's statement: " + norm(sub.rstrip("."))), line)
                for p in task.get("parameters") or []:
                    for cond in p["range"].split(", "):
                        self.assertIn(cond, line)
                if not task.get("parameters"):
                    self.assertIn("at its one fixed size", line)
                secs = ((rec or {}).get("proof") or {}).get("build_seconds")
                runs = ((limits.get(t) or {}).get("references") or {}).get(stem or "", {}).get("wall_s") or []
                if rec is not None:
                    self.assertIn(f"the proof built in {secs:g} s when checked", line)
                elif runs:
                    lo, hi = min(runs), max(runs)
                    self.assertIn(f"the proof built in {lo:g} to {hi:g} s in {len(runs)} cold runs", line)
                else:
                    self.assertNotRegex(line, r"\d s\b")
                self.assertNotIn("<p", first.group(1))

    def test_the_tab_bar_stays_at_the_top(self):
        """Decided 2026-11-16 (the owner's item 2, "Make the tab bar sticky"): with the script (site.js has made the
        tabs: `.js-tabs`), on screen, the page's tab bar sticks to the top of the view while a pane scrolls under it;
        without the script it neither sticks nor scrolls, and printed it is not there. On a phone it is one line that
        scrolls sideways inside itself (stuck or not), a fade at an edge where more tabs are. What is brought into view
        in a pane keeps clear of it (a scroll margin of the bar's height, `--tabs-bar`). site.js's part (`--tabs-bar`,
        a tab chosen in the stuck bar) is tabsjs_check.js's; the real page's, the round's headless check's (fragments
        and the keyboard's focus land below the bar)."""
        css = open(os.path.join(SITE, "style.css"), encoding="utf-8").read()
        sticky = [m for m in re.finditer(r"([^{}]+)\{[^{}]*position: sticky;[^{}]*\}", css) if "tabs-nav" in m.group(1)]
        self.assertTrue(sticky)
        for m in sticky:
            self.assertIn(".tabs-page.js-tabs > .tabs-nav", m.group(1))
            before = css[:m.start()]
            self.assertEqual(before.rfind("@media screen"), max(before.rfind("@media"), before.rfind("@media screen")))
        bar = css[css.index("THE BAR STAYS"):]
        phone = bar[bar.index("@media screen and (max-width: 40rem) {"):]
        phone = phone[:phone.index("\n}\n")]
        self.assertRegex(phone, r"\.tabs-page\.js-tabs > \.tabs-nav \{ flex-wrap: nowrap; overflow-x: auto;")
        self.assertIn(".tabs-page.js-tabs > .tabs-nav.at-end::after", phone)
        self.assertIn(".tabs-page.js-tabs > .tabs-nav.at-start::before", phone)
        printed = css[css.index("@media print {"):]
        self.assertIn(".tabs-nav, .sch-tools { display: none; }", printed)
        js = open(os.path.join(SITE, "site.js"), encoding="utf-8").read()
        self.assertIn('st.setProperty("--tabs-bar", v)', js)
        # the panes and what a link, a fragment or the focus brings into view in them keep clear of the stuck bar
        self.assertRegex(css, r"\.tabs-page\.js-tabs > \.tabs-pane :where\(\[id\], a, button, summary, input, select, "
                              r"textarea, \[tabindex\]\) \{\s*scroll-margin-top: var\(--tabs-bar, 0px\); \}")

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
