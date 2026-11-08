"""The detail pages of the site: one per record and one per proved reference without a record (PLAN4 3b step 3):
the dashboard (Area, Performance and Score cards with their beats/matches lines), the area-time plot, the schematic
of the display instance, the critical path, the cells, the sources, reproduce. Built once with --offline.

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

    def page(self, path):
        return self.files[path].decode("utf-8")

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
            for ref in task.get("references", []):
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
            self.assertEqual(len(mine), len(task["references"]), t)
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
        self.assertTrue(self.previews, "config.json lists previews")
        for t in self.previews:
            with self.subTest(task=t):
                task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
                pages = [p for p in self.files if p.startswith((f"tasks/{t}/records/", f"tasks/{t}/reference/"))
                         and p.endswith(".html")]
                self.assertEqual(pages, [])
                task_html = self.page(f"tasks/{t}/index.html")
                refs = section(task_html, "references")
                for ref in task.get("references", []):
                    stem = posixpath.splitext(posixpath.basename(ref["sv"]))[0]
                    self.assertIn(f'id="ref-{stem}"', refs)
                    self.assertNotIn(f'href="reference/{stem}.html"', task_html)
                for m in re.finditer(r'<a href="([^"]+)" aria-label="[^"]*"><g class="mark[^"]*" data-kind="reference"',
                                     task_html):
                    self.assertRegex(m.group(1), r"^index\.html#ref-[A-Za-z0-9_]+$")
                for path in (p for p in self.files if p.startswith(f"tasks/{t}/") and p.endswith(".html")):
                    self.assertNotIn("· ranked", text_of(self.page(path)), path)

    def test_every_detail_page_has_its_sections_in_order(self):
        order = ("dashboard", "area-time", "schematic", "critical-path", "cells", "sources", "reproduce")
        for t, path, rec, stem in self.detail_pages():
            with self.subTest(page=path):
                h = self.page(path)
                if "No ranked numbers to show" in text_of(section(h, "dashboard")):
                    order = tuple(o for o in order if o != "area-time")
                at = [h.find(f'id="{sid}"') for sid in order]
                self.assertTrue(all(a >= 0 for a in at), dict(zip(order, at)))
                self.assertEqual(at, sorted(at))
                self.assertIn('src="../../../charts.js"', h)

    def test_the_cards_show_the_ranked_numbers(self):
        """The Area, Performance and Score cards: the record's own sky130 columns (a reference without a record: its
        golden), exact, with the beats/matches line empty while the task has no other player."""
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
                for label in ("Area", "Performance · time", "Score · area × time", "On the Pareto board"):
                    self.assertIn(label, dash)
                self.assertIn(f"{lb.fmt_um2(cols['area_e4um2'])} µm² exactly", dash)
                self.assertIn(norm(f"{cols['time_ps']:,}".replace(",", " ")) + "ps", dash)
                score = build.combined.fmt(build.combined.um2ns(cols["area_e4um2"] * cols["time_ps"]))
                self.assertIn(norm(score), dash)
                players = {r["player"] for r in self.recs if r["task"] == t and r["player"] != self.config["reference_player"]}
                if not players:
                    self.assertIn("Beats – · matches –", dash)
                    self.assertNotRegex(dash, r"Beats \d")
                    self.assertIn("(0 players, 0 records)", dash)
        self.assertGreaterEqual(shown, 15)

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
                    self.assertIn("Every number on this page outside this card is the scored one", text_of(sch))
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
