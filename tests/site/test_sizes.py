"""The charts' Size selector (decided 2026-11-13, the owner's UI feedback item 11: "we should still synthesize for more
N ... and make it possible to choose in the graph ... that way we can see which designs scale better"): site/build.py
`load_sizes` reads leaderboard/sizes/<task>.json, the file `leaderboard.py sizes --write` writes (schema
svgolf-sizes/1), and `point_views` draws every design of a task page at each size: its design file's numbers there (a
record's, par's), else score/measured/'s (a reference's, a baseline's), the designs measured at neither left out with
the reason. Checked here against the two data files read independently of the generator; the routed course's selector
holds the scoring size alone, disabled; without a sizes file the pages still build.

    python3.12 svgolf/tests/site/test_sizes.py
"""

import contextlib
import glob
import hashlib
import html
import importlib.util
import io
import json
import os
import re
import sys
import tempfile
import types
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
sys.path.insert(0, SITE)

spec = importlib.util.spec_from_file_location("svgolf_site_build_sizes", os.path.join(SITE, "build.py"))
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)
lb = build.lb
SKY_ONLY = "other sizes are measured on sky130 only"


def load(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def sizes_file(t):
    path = os.path.join(SVGOLF, "leaderboard", "sizes", f"{t}.json")
    return load(path) if os.path.isfile(path) else None


def measured_file(t):
    path = os.path.join(SVGOLF, "score", "measured", f"{t}.json")
    return load(path) if os.path.isfile(path) else None


def file_sha(rel):
    with open(os.path.join(SVGOLF, rel), "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def design_shas(t):
    """{a page design's id: its design file's sha256}: a record's from its stored record, a reference's from task.json's
    file, a baseline's from score/measured/ (read here, not from the generator)."""
    out = {}
    for path in glob.glob(os.path.join(SVGOLF, "leaderboard", "data", t, "*.json")):
        rec = load(path)
        out[rec["record_hash"]] = rec["files"]["sv"]["sha256"]
    task = lb.load_task(os.path.join(SVGOLF, "tasks"), t)
    for ref in task.get("references", []):
        stem = os.path.splitext(os.path.basename(ref["sv"]))[0]
        out[f"reference/{stem}"] = file_sha(f"tasks/{t}/{ref['sv']}")
    for e in (measured_file(t) or {}).get("designs", []):
        out.setdefault(e["id"], e["sha256"])
    return out


def page_data(files, t, pdk=""):
    m = re.search(r'<script type="application/json" id="task-data' + (f"-{pdk}" if pdk else "") + r'">(.*?)</script>',
                  files[f"tasks/{t}/index.html"], re.S)
    return json.loads(m.group(1)) if m else None


def build_into(out, **patches):
    with contextlib.ExitStack() as stack:
        for name, value in patches.items():
            stack.enter_context(mock.patch.object(build, name, value))
        stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
        stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
        rc = build.main(["--offline", "--out", out])
    files = {}
    for root, _, names in os.walk(out):
        for n in names:
            if n.endswith(".html"):
                p = os.path.join(root, n)
                with open(p, encoding="utf-8") as fh:
                    files[os.path.relpath(p, out).replace(os.sep, "/")] = fh.read()
    return rc, files


class SizesSite(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        rc, cls.files = build_into(os.path.join(cls.tmp.name, "site"))
        if rc != 0:
            raise AssertionError(f"build.py --offline exited {rc}")
        cls.tasks = sorted(os.path.basename(p)[:-5] for p in glob.glob(os.path.join(SVGOLF, "leaderboard", "sizes",
                                                                                     "*.json")))

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_the_sizes_are_the_generator_s(self):
        """The selector's sizes are the sizes file's, in its order (then any point of score/measured/ it lacks), the
        scoring one marked; a task has one file or none (aes_sbox: no parameter, no selector)."""
        self.assertGreaterEqual(len(self.tasks), 8)
        for t in self.tasks:
            with self.subTest(task=t):
                sz, data = sizes_file(t), page_data(self.files, t)
                self.assertEqual(sz["schema"], "svgolf-sizes/1")
                keys = [x["key"] for x in sz["sizes"]]
                keys += [p["key"] for p in (measured_file(t) or {}).get("points", []) if p["key"] not in keys]
                self.assertEqual([p["key"] for p in data["points"]], keys)
                self.assertEqual([p["key"] for p in data["points"] if p["scored"]], [sz["scored"]])
                html_ = self.files[f"tasks/{t}/index.html"]
                self.assertIn('<select id="explore-size" data-size-select>', html_)
        self.assertIsNone(page_data(self.files, "aes_sbox").get("points"))
        self.assertNotIn("data-size-select", self.files["tasks/aes_sbox/index.html"])

    def test_every_design_at_every_size_or_counted_with_its_reason(self):
        """At each other size every design of the page is drawn with its design file's numbers there (the sizes file:
        area, time, score, depth, GE, cycles), else score/measured/'s, or it is counted as not measured with the
        reason: the sizes file's (a run past a limit), score/measured/'s drop, or "not measured at this size"."""
        for t in self.tasks:
            sz, me, data = sizes_file(t), measured_file(t), page_data(self.files, t)
            by_sha = {e["sv_sha256"]: e for e in sz["designs"]}
            by_id = {e["id"]: e for e in (me or {}).get("designs", [])}
            shas = design_shas(t)
            for p in data["points"]:
                if p["scored"]:
                    continue
                at = {d["id"]: d for d in data["at"].get(p["key"], [])}
                missing = {m[0]: m[1] for m in p["missing"]}
                for d in data["designs"]:
                    with self.subTest(task=t, size=p["key"], design=d["id"]):
                        x = (by_sha.get(shas.get(d["id"])) or {}).get("at", {}).get(p["key"])
                        e = by_id.get(d["id"])
                        label = (f"{d['title']} · " if d.get("title") and d["title"] != d["name"] else "") + d["name"]
                        if x and x["status"] == "measured":
                            got = at[d["id"]]["m"]
                            self.assertEqual(got["area_um2"], x["area_e4um2"] / 10000)
                            self.assertEqual(got["time_ps"], x["time_ps"])
                            self.assertEqual(got["adp"], x["area_x_time"] / 10_000_000)
                            self.assertEqual(got["depth"], x["depth"])
                            self.assertEqual(round(got["area_ge"] * 1000), x["area_mge"])
                            if x["cycles"] is not None:
                                self.assertEqual((got["cycles"], got["period_ps"]), (x["cycles"], x["delay_ps"]))
                            self.assertTrue(at[d["id"]]["measured"])
                            self.assertNotIn(label, missing)
                        elif e is not None and p["key"] in e["at"]:
                            self.assertEqual(at[d["id"]]["m"]["area_um2"], e["at"][p["key"]]["area_e4um2"] / 10000)
                        else:
                            self.assertNotIn(d["id"], at)
                            want = (x or {}).get("reason") or ((e or {}).get("dropped") or {}).get(p["key"]) \
                                or "not measured at this size"
                            self.assertEqual(missing.get(label), want)

    def test_the_limits_are_counted(self):
        """The runs past a limit are counted at their size, with the sizes file's reason (two on 2026-11-13 before the
        matmul records' sizes)."""
        seen = 0
        for t in self.tasks:
            data = page_data(self.files, t)
            for e in sizes_file(t)["designs"]:
                for key, x in e["at"].items():
                    if x["status"] == "not measured":
                        p = next(p for p in data["points"] if p["key"] == key)
                        self.assertIn(x["reason"], [m[1] for m in p["missing"]], (t, key))
                        seen += 1
        self.assertGreaterEqual(seen, 2)

    def test_par_at_each_size(self):
        """Par's point at each size is par's design (the sizes file's `par` entry): the same id as at the scoring size,
        its numbers there; the other designs are never par."""
        for t in self.tasks:
            sz, data = sizes_file(t), page_data(self.files, t)
            par_ids = [d["id"] for d in data["designs"] if d["par"]]
            par_files = [e for e in sz["designs"] if e["par"]]
            if not par_ids:
                continue
            self.assertEqual(len(par_files), 1, t)
            shas = design_shas(t)
            for p in data["points"]:
                if p["scored"]:
                    continue
                with self.subTest(task=t, size=p["key"]):
                    pars = [d for d in data["at"].get(p["key"], []) if d["par"]]
                    x = par_files[0]["at"][p["key"]]
                    if x["status"] != "measured":
                        self.assertEqual(pars, [])
                        continue
                    self.assertEqual(sorted(d["id"] for d in pars), sorted(par_ids))
                    for d in pars:
                        self.assertEqual(shas[d["id"]], par_files[0]["sv_sha256"])
                        self.assertEqual(d["m"]["adp"], x["area_x_time"] / 10_000_000)

    def test_the_scoring_size_is_the_ranked_one(self):
        """At the scoring size the page draws its ranked numbers, and they equal the sizes file's entry for every
        record's design file there (the control, as the page sees it)."""
        for t in self.tasks:
            sz, data = sizes_file(t), page_data(self.files, t)
            shas = design_shas(t)
            by_sha = {e["sv_sha256"]: e for e in sz["designs"]}
            for d in data["designs"]:
                e = by_sha.get(shas.get(d["id"]))
                if e is None or d["kind"] == "baseline" or "area_um2" not in d["m"]:
                    continue                     # a second proof without its own sky130 weighing (band_tactics)
                with self.subTest(task=t, design=d["id"]):
                    x = e["at"][sz["scored"]]
                    self.assertEqual((d["m"]["area_um2"], d["m"]["time_ps"]), (x["area_e4um2"] / 10000, x["time_ps"]))
                    self.assertNotIn("measured", d)

    def test_the_size_axes(self):
        """The explorer's X axis "Size": one option per series of the sizes file, its keys in order and each key's x
        the parameter's value; the Y axis's "÷ par" beside it when the task has par."""
        for t in self.tasks:
            with self.subTest(task=t):
                sz, data = sizes_file(t), page_data(self.files, t)
                self.assertEqual([ax["keys"] for ax in data["sizes"]], [s["keys"] for s in sz["series"]])
                params = {x["key"]: x["params"] for x in sz["sizes"]}
                for ax, s in zip(data["sizes"], sz["series"]):
                    self.assertEqual(ax["param"], s["param"])
                    self.assertEqual(ax["x"], {k: params[k][s["param"]] for k in s["keys"]})
                html_ = self.files[f"tasks/{t}/index.html"]
                xsel = html_.split('<select id="explore-x" data-axis="x">', 1)[1].split("</select>", 1)[0]
                self.assertEqual(re.findall(r'<option value="(size:\d+)">', xsel),
                                 [f"size:{k}" for k in range(len(sz["series"]))])
                self.assertEqual("data-size-rel" in html_.split('id="explore-y"', 1)[1].split("</div>", 1)[0],
                                 any(d["par"] for d in data["designs"]))

    def test_the_head_tag_and_the_legend_count(self):
        """The chart head carries the "not ranked" tag (hidden; charts.js shows it at another size) linking the rules
        page's "Other sizes", on sky130 only; the legend line has the count's item (hidden); no note above the chart."""
        for t in self.tasks:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"]
                head = html_.split('id="explore"', 1)[1].split('<div class="chart-slot"', 1)[0]
                self.assertRegex(head, r'<span class="pdk-sky130 size-tag" data-size-tag hidden><a href="\.\./\.\./rules'
                                       r'\.html#other-sizes">not ranked · <span data-size-tag-at>')
                self.assertIn("<span data-size-words>any two numbers</span>", head)
                self.assertIn('<li class="size-missing" data-size-missing hidden tabindex="0"></li>', html_)
                self.assertNotIn("data-point-note", html_)
        self.assertIn('id="other-sizes"', self.files["rules.html"])

    def test_the_routed_course_has_the_scoring_size_only(self):
        """On the routed course the Size selector holds the scoring size alone, disabled, its hover text saying why; the
        routed explorer's data has no other size and its X axis no Size option; a record page's routed plot likewise."""
        for t in self.tasks:
            with self.subTest(task=t):
                html_ = self.files[f"tasks/{t}/index.html"]
                ex = html_.split('id="explore"', 1)[1]
                routed = ex.split('<div class="pdk pdk-asap7pnr">', 1)[1]
                m = re.search(r'<div class="axis-control size-control" title="([^"]+)"><label class="label" '
                              r'for="explore-size-asap7pnr">Size</label><select id="explore-size-asap7pnr" '
                              r'data-size-select disabled title="([^"]+)">(.*?)</select>', routed, re.S)
                self.assertIsNotNone(m)
                self.assertEqual((html.unescape(m.group(1)), html.unescape(m.group(2))), (SKY_ONLY, SKY_ONLY))
                opts = re.findall(r'<option value="([^"]+)" selected>([^<]*)</option>', m.group(3))
                self.assertEqual(len(opts), 1)
                self.assertEqual(opts[0][0], sizes_file(t)["scored"])
                self.assertTrue(opts[0][1].endswith("· scored"))
                rd = page_data(self.files, t, "asap7pnr")
                if rd is not None:
                    self.assertNotIn("points", rd)
                xsel = routed.split('data-axis="x">', 1)[1].split("</select>", 1)[0]
                self.assertNotIn('value="size:', xsel)
        rec = next(p for p in self.files if p.startswith("tasks/mul/records/") and p.endswith(".html")
                   and "area-time-size-asap7pnr" in self.files[p])
        self.assertRegex(self.files[rec], r'<select id="area-time-size-asap7pnr" data-size-select disabled title="'
                                          + re.escape(SKY_ONLY) + r'"><option value="N=16" selected>N = 16 · scored'
                                          r'</option></select>')

    def test_a_record_page_draws_every_size(self):
        """A record's "Area against time": the server draws the plot at every size of the task where designs have area
        and time (each `data-at`, wide and compact, the fit view; the scoring size's shown, the others hidden), with the
        Size selector beside "Fit to cluster" / "All designs"; the slot's data names each size's missing designs and
        par's score there (par's sizes-file product, as the legend writes it)."""
        sz = sizes_file("mul")
        par_file = next(e for e in sz["designs"] if e["par"])
        checked = 0
        for e in sz["designs"]:
            for r in e["records"]:
                page = f"tasks/mul/records/{r['record_hash']}.html"
                if page not in self.files:
                    continue
                checked += 1
                with self.subTest(record=r["record_hash"][:12]):
                    h = self.files[page]
                    sky = h.split('id="area-time"', 1)[1].split('<div class="pdk pdk-asap7pnr">', 1)[0]
                    keys = [x["key"] for x in sz["sizes"]]
                    for key in keys:
                        for size in ("wide", "compact"):
                            hidden = "" if key == sz["scored"] else " hidden"
                            self.assertIn(f'<div class="chart-variant" data-at="{key}" data-view="fit" '
                                          f'data-size="{size}"{hidden}>', sky)
                    self.assertIn('<select id="area-time-size" data-size-select>', sky)
                    info = json.loads(re.search(r'<script type="application/json" data-at-info>(.*?)</script>', sky,
                                                re.S).group(1))
                    self.assertEqual(sorted(info), sorted(keys))
                    for key in keys:
                        x = par_file["at"][key]
                        self.assertEqual(info[key]["par"], build.combined.fmt(x["area_x_time"] / 10_000_000), key)
                        self.assertEqual(info[key]["scored"], key == sz["scored"])
                        mine = e["at"][key]["status"] == "measured"
                        self.assertEqual("this design" in [m[0] for m in info[key]["missing"]], not mine, key)
                    self.assertRegex(h, r'<span class="pdk-sky130 size-tag" data-size-tag hidden><a href="\.\./\.\./\.\./'
                                        r'rules\.html#other-sizes">not ranked · ')
        self.assertGreaterEqual(checked, 7)


class WithoutSizes(unittest.TestCase):
    def test_without_a_sizes_file_the_pages_still_build(self):
        """With no leaderboard/sizes/ at all the site builds as before the data existed: the selector is score/measured/'s
        points (references and baselines), the record pages' plots the scoring size and those points."""
        with tempfile.TemporaryDirectory() as tmp:
            rc, files = build_into(os.path.join(tmp, "site"), SIZES="svgolf/leaderboard/no-sizes-here")
            self.assertEqual(rc, 0)
            for t in ("mul", "matmul", "aes_sbox"):
                data = page_data(files, t)
                me = measured_file(t)
                keys = [p["key"] for p in me["points"]] if me and len(me["points"]) > 1 else None
                self.assertEqual([p["key"] for p in data["points"]] if "points" in data else None, keys, t)
            self.assertTrue(any(p.startswith("tasks/matmul/records/") for p in files))

    def test_a_stale_sizes_file_is_not_drawn(self):
        """A sizes file measured under other pins than the page's (here: other limits) is not drawn: a warning, fatal
        under --strict, and the task falls back to score/measured/'s points."""
        real = build.read_text

        def stale(rel):
            text = real(rel)
            if rel == f"{build.SIZES}/mul.json":
                data = json.loads(text)
                data["pins"]["limits"] = {"timeout_s": 1, "memory_gb": 1}
                return json.dumps(data)
            return text
        warned = []
        site = types.SimpleNamespace(ppa_identity=lb.ppa_identity(), a7_identity=lb.asap7_identity(),
                                     warn=warned.append)
        task = lb.load_task(os.path.join(SVGOLF, "tasks"), "mul")
        exp = load(os.path.join(SVGOLF, "tests", "expected.json"))
        flow = {"yosys": exp["flow"]["yosys_version"], "canon_script_sha256": exp["flow"]["canon_script_sha256"],
                "script_sha256": exp["flow"]["script_sha256"], "ge_table_sha256": exp["flow"]["ge_table_sha256"]}
        t = types.SimpleNamespace(name="mul", point_key="N=16", task=task, flow=flow,
                                  drive=lb.ppa_setup_now(task).get("input_drive"))
        self.assertIsNotNone(build.load_sizes(site, t))
        self.assertEqual(warned, [])
        with mock.patch.object(build, "read_text", stale):
            self.assertIsNone(build.load_sizes(site, t))
        self.assertEqual(len(warned), 1)
        self.assertIn("measured under other pins than now (limits differ)", warned[0])


if __name__ == "__main__":
    unittest.main()
