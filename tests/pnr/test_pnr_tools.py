#!/usr/bin/env python3.12
"""The routed course's run tools (score/pnr/: job.py, run_job.py, collect.py, encode.py, check_sitedata.py), offline on
stored run data (tests/pnr/fixtures/README.txt says where each fixture comes from). No container, no OpenROAD, no Lean.

  - the generator renders the config.mk and SDC of EVERY committed run (leaderboard/asap7pnr) to their recorded
    sha256, and writes the stored job's files byte for byte; the ORFS values come from score/pnr/pins.json; the two
    pinned renderers are in the tree with the pinned sha256;
  - the runner's container command (by digest, no network, the pinned CPUs and memory cap, inputs read-only) and its
    refusal of a config.mk made under other pins;
  - the collector: a row from the files fetched back of a run (hashes, cell histogram, the equivalence verdict), ORFS's
    raw metric texts kept as text, the normalized SPEF hash; and the whole path render -> picture -> entry -> site
    data -> `leaderboard.py asap7pnr --import` reproducing the committed leaderboard/asap7pnr/_example.json, byte for
    byte, from the stored job of _example's band_lp design;
  - the site-data check: clean on that data, and each planted fault caught.

The area needs the pinned ASAP7 liberty (`score/ppa.py --pdk asap7 --fetch-liberty`, or $SVGOLF_ASAP7_LIB); without
it the one cell the fixture uses is given its area here (0.08748 um^2, AND2x2_ASAP7_75t_R), which a test holds to the
liberty wherever the liberty is present. The picture is encoded again from the stored render where Pillow 11.1.0 and
libwebp 1.5.0 are installed (what the committed pictures were made with); elsewhere the committed picture files stand
in for the encoder's output and the encoder's own test is skipped.

    python3.12 tests/pnr/test_pnr_tools.py
"""

import copy
import json
import os
import shutil
import sys
import tempfile
import unittest
from decimal import Decimal

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "score", "pnr"))
sys.path.insert(0, os.path.join(SVGOLF, "leaderboard"))
import check_sitedata  # noqa: E402
import collect  # noqa: E402
import encode  # noqa: E402
import job as jobmod  # noqa: E402
import leaderboard as lb  # noqa: E402
import pnr  # noqa: E402
import run_job  # noqa: E402

FIX = os.path.join(HERE, "fixtures")
EXJOB_DIR = os.path.join(FIX, "example_job")
EXJOB = "_example_38596d52847c__min_s1"
EXNICK = "_example_38596d52847c"
BAND_LP = "a5784d61a37a73102d0f55bb15fa259a55a1a303aa490d4fd01aa73ce97766c4"   # _example's band_lp design file
ADD_JOB = "add_3f31f3f29548__min_s1"
AND2_AREA = Decimal("0.08748")


def read(path, mode="r"):
    with open(path, mode) as fh:
        return fh.read()


def write(path, blob):
    with open(path, "wb") as fh:
        fh.write(blob)


def committed(task):
    with open(os.path.join(SVGOLF, "leaderboard", "asap7pnr", f"{task}.json"), encoding="utf-8") as fh:
        text = fh.read()
    return text, json.loads(text)


def liberty_present():
    try:
        collect.liberty_areas()
        return True
    except collect.CollectError:
        return False


def areas():
    return collect.liberty_areas() if liberty_present() else {"AND2x2_ASAP7_75t_R": AND2_AREA}


def area_of():
    if liberty_present():
        return check_sitedata.liberty_area_reader()
    return {"AND2x2_ASAP7_75t_R": AND2_AREA}.get


def encoder_matches():
    return encode.pillow_version() == encode.COMMITTED_WITH


def tree_layout_to_images(L):
    L = copy.deepcopy(L)
    for key in ("image", "thumb"):
        L[key] = "images/" + L[key][len(lb.PNR_LAYOUTS) + 1:]
    return L


def pending_tree(table, sv):
    """The table as it was before the design's run: its entry pending, its request kept."""
    t = copy.deepcopy(table)
    e = lb.asap7pnr_entry(t, sv)
    e.update(runs=[], scores={"v_owner": None, "v_median": None}, status="pending", layout=None)
    return t


def picture_record(out_dir, committed_entry):
    """encode.py's record of the stored render, its files written to out_dir/images/_example/; without the committed
    Pillow and libwebp the committed picture files stand in (their quality read from the committed entry)."""
    with open(os.path.join(EXJOB_DIR, "img", EXJOB + ".png"), "rb") as fh:
        png = fh.read()
    d = os.path.join(out_dir, "images", "_example")
    os.makedirs(d, exist_ok=True)
    sv16 = BAND_LP[:16]
    if encoder_matches():
        pic, thumb, rec = encode.encode(png)
    else:
        L = committed_entry["layout"]
        pic, thumb = (read(os.path.join(SVGOLF, *L[k].split("/")), "rb") for k in ("image", "thumb"))
        rec = {"png_sha256": pnr.sha256_bytes(png), "png_px": check_sitedata._png_px(png),
               "px": list(lb.webp_size(pic)), "quality": L["webp_quality"], "bytes": len(pic),
               "sha256": pnr.sha256_bytes(pic), "thumb_px": list(lb.webp_size(thumb)), "thumb_bytes": len(thumb),
               "thumb_sha256": pnr.sha256_bytes(thumb)}
    for name, blob in ((f"{sv16}.webp", pic), (f"{sv16}.thumb.webp", thumb)):
        with open(os.path.join(d, name), "wb") as fh:
            fh.write(blob)
    return rec


def collected_entry(out_dir, table, **over):
    """collect.py's entry of the band_lp design from the stored job (keyword overrides of build_entry's inputs)."""
    task, view, _t, designs = collect.tree_context("_example")
    ce = lb.asap7pnr_entry(table, BAND_LP)
    with open(os.path.join(EXJOB_DIR, "rows", EXJOB + ".json"), encoding="utf-8") as fh:
        row = json.load(fh)
    kw = dict(task_name="_example", view_entry=lb.asap7_entry(view, BAND_LP), of=designs[BAND_LP]["of"],
              request=copy.deepcopy(ce["request"]), row=row,
              mk_bytes=read(os.path.join(EXJOB_DIR, "cfg", EXJOB + ".mk"), "rb"),
              sdc_bytes=read(os.path.join(EXJOB_DIR, "sdc", EXNICK + ".sdc"), "rb"),
              host=json.loads(read(os.path.join(EXJOB_DIR, "logs", EXJOB + ".host.json"))), date="2026-11-13",
              picture=picture_record(out_dir, ce), render_log=read(os.path.join(EXJOB_DIR, "logs", EXJOB + ".render.out")),
              areas=areas(), pins=pnr.load_pins())
    kw.update(over)
    return collect.build_entry(**kw), view


def designs_of(task_name):
    task = lb.load_task(lb.DEFAULT_TASKS, task_name)
    with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
        expected = json.load(fh)
    return lb.asap7_designs(task, lb.good_records(lb.load_records(lb.DEFAULT_DATA)), expected)


class TempDir(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="pnrtools-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)


class GeneratorTest(TempDir):
    def test_every_committed_run_renders_to_its_recorded_files(self):
        """job.py renders the config.mk and SDC of every run in leaderboard/asap7pnr (scoring and spread, three
        campaigns, both renderers' jobs) to the sha256 the run records."""
        pins, n = pnr.load_pins(), 0
        for f in sorted(os.listdir(os.path.join(SVGOLF, "leaderboard", "asap7pnr"))):
            task, view = jobmod.load_tree(f[:-5])
            for e in committed(f[:-5])[1]["designs"]:
                for r in e["runs"]:
                    with self.subTest(task=f[:-5], design=e["sv_sha256"][:12], seed=r["seed"]):
                        _j, _mk, _sdc, rec = jobmod.render(task, view, e["netlist_sha256"], r["seed"], pins)
                        self.assertEqual((rec["config_mk_sha256"], rec["sdc_sha256"]),
                                         (r["config_mk_sha256"], r["sdc_sha256"]))
                        n += 1
        self.assertGreaterEqual(n, 97)

    def test_the_stored_job_byte_for_byte(self):
        rec = jobmod.write_job(self.tmp, os.path.join(EXJOB_DIR, "designs", EXNICK + ".v"),
                               *jobmod.load_tree("_example"), 1, pnr.load_pins())
        self.assertEqual(rec["job"], EXJOB)
        for rel in (("designs", EXNICK + ".v"), ("sdc", EXNICK + ".sdc"), ("cfg", EXJOB + ".mk")):
            with self.subTest(file=rel):
                self.assertEqual(read(os.path.join(self.tmp, *rel), "rb"),
                                 read(os.path.join(EXJOB_DIR, *rel), "rb"))
        run = lb.asap7pnr_entry(committed("_example")[1], BAND_LP)["runs"][0]
        self.assertEqual((rec["config_mk_sha256"], rec["sdc_sha256"], rec["io_tcl_sha256"]),
                         (run["config_mk_sha256"], run["sdc_sha256"], None))
        self.assertEqual((rec["clock_period_ps"], rec["seq"], rec["cells"], rec["seed"]), (56.0, False, 16, 1))
        self.assertTrue(os.path.isfile(os.path.join(self.tmp, "jobs", EXJOB + ".json")))
        self.assertEqual(jobmod.main(["--task", "_example", "--netlist", os.path.join(EXJOB_DIR, "designs", EXNICK + ".v"),
                                      "--seed", "2", "--out", self.tmp]), 0)
        self.assertTrue(os.path.isfile(os.path.join(self.tmp, "cfg", EXNICK + "__min_s2.mk")))

    def test_values_come_from_the_pins(self):
        task, view = jobmod.load_tree("_example")
        pins = copy.deepcopy(pnr.load_pins())
        pins["orfs_variables"]["CORE_UTILIZATION"] = "50"
        _j, mk, _s, _r = jobmod.render(task, view, "38596d52847c91d7e7fd70188696e9e46d40313f3f301d368705a0864dcb4902",
                                       1, pins)
        self.assertIn("export CORE_UTILIZATION = 50\n", mk)
        pins["orfs_variables"]["NEW_VARIABLE"] = "1"
        with self.assertRaises(jobmod.JobError):
            jobmod.render(task, view, "38596d52847c91d7e7fd70188696e9e46d40313f3f301d368705a0864dcb4902", 1, pins)

    def test_refusals(self):
        task, view = jobmod.load_tree("_example")
        pins = pnr.load_pins()
        for seed in (0, 2 ** 31, "1"):
            with self.subTest(seed=seed), self.assertRaises(jobmod.JobError):
                jobmod.render(task, view, "38596d52847c91d7e7fd70188696e9e46d40313f3f301d368705a0864dcb4902", seed, pins)
        with self.assertRaises(jobmod.JobError):
            jobmod.render(task, view, "0" * 64, 1, pins)

    def test_the_pinned_renderers_are_in_the_tree(self):
        """score/pnr/pins.json pins the sha256 of the campaign renderers; the files are kept byte for byte."""
        for name, sha in pnr.load_pins()["renderers"].items():
            with self.subTest(renderer=name):
                self.assertEqual(pnr.sha256_file(os.path.join(SVGOLF, "score", "pnr", name)), sha)


class RunnerTest(TempDir):
    def test_the_container_command(self):
        pins = pnr.load_pins()
        cmd = run_job.run_command(EXJOB_DIR, EXJOB, pins, runtime="docker")
        text = " ".join(cmd)
        self.assertEqual(cmd[:4], ["docker", "run", "--rm", "--network"])
        self.assertIn(f"docker.io/openroad/orfs@{pins['image']['manifest_digest']}", cmd)
        self.assertNotIn(pins["image"]["tag"], text)                         # by digest, never by tag
        for opt, val in (("--network", "none"), ("--cpus", "2"), ("--cpuset-cpus", "0-1"), ("--memory", "8g"),
                         ("--memory-swap", "8g"), ("--platform", "linux/amd64"), ("-w", pnr.FLOW_DIR)):
            self.assertEqual(cmd[cmd.index(opt) + 1], val, opt)
        mounts = {inside: ro for _h, inside, ro in run_job._mounts_of(cmd)}
        self.assertEqual(mounts, {"/work/designs": True, "/work/sdc": True, "/work/cfg": True, "/work/run": False,
                                  "/tmp": False})
        self.assertIn(f"make DESIGN_CONFIG=/work/cfg/{EXJOB}.mk", cmd[-1])
        self.assertEqual(run_job.run_command(EXJOB_DIR, EXJOB, pins, runtime="podman", cpuset="4-5")[0], "podman")
        self.assertEqual(run_job.main(["run", EXJOB_DIR, EXJOB, "--dry-run"]), 0)

    def test_a_job_under_other_pins_is_refused(self):
        d = os.path.join(self.tmp, "job")
        shutil.copytree(EXJOB_DIR, d)
        mk = os.path.join(d, "cfg", EXJOB + ".mk")
        text = read(mk)
        for bad in (text.replace("PLACE_DENSITY = 0.60", "PLACE_DENSITY = 0.70"), text + "export EXTRA_THING = 1\n",
                    text.replace("GPL_RANDOM_SEED = 1", "GPL_RANDOM_SEED = 2"),
                    text.replace("NUM_CORES = 2", "NUM_CORES = 4")):
            with self.subTest(bad=bad[-60:]):
                with open(mk, "w") as fh:
                    fh.write(bad)
                with self.assertRaises(ValueError):
                    run_job.run_command(d, EXJOB, pnr.load_pins())
                self.assertEqual(run_job.main(["run", d, EXJOB, "--dry-run"]), 2)

    def test_the_render_command(self):
        d = os.path.join(self.tmp, "job")
        shutil.copytree(EXJOB_DIR, d)
        with self.assertRaises(ValueError):                                  # no run yet: nothing to draw
            run_job.render_command(d, EXJOB, pnr.load_pins())
        res = pnr.work_dirs(d, EXJOB)["results"]
        os.makedirs(res)
        write(os.path.join(res, "6_final.odb"), b"")
        cmd = run_job.render_command(d, EXJOB, pnr.load_pins())
        mounts = {inside: ro for _h, inside, ro in run_job._mounts_of(cmd)}
        self.assertTrue(mounts["/srv"] and mounts["/work/tools"])            # the scored run and the scripts read-only
        self.assertIn(f"ODB_FILE=/srv/results/asap7/{EXNICK}/min_s1/6_final.odb", cmd)
        self.assertIn("-exit /work/tools/layout.tcl", cmd[-1])


class CollectorTest(TempDir):
    def test_a_row_from_the_files_fetched_back(self):
        """The files of the 2026-11-13 re-run of add's par design that came back from the course host: their hashes,
        cell histogram and equivalence verdict are those the committed entry records for the run it reproduced."""
        row = collect.collect_row(os.path.join(FIX, "add_rerun"), ADD_JOB)
        self.assertEqual((row["status"], row["rc"], row["seconds"], row["cpus"], row["date"]),
                         ("ok", 0, 64.2, "0-1", "2026-11-13"))
        self.assertNotIn("host", row)
        add = next(e for e in committed("add")[1]["designs"] if e["netlist_sha256"].startswith("3f31f3f29548"))
        run = next(r for r in add["runs"] if r["role"] == "scoring")
        self.assertEqual(row["sha256"]["1_2_yosys.v"], run["artifacts"]["1_2_yosys.v"])
        self.assertEqual(row["sha256"]["6_final.v"], run["artifacts"]["6_final.v"])
        self.assertEqual(sum(row["final_hist"].values()), run["cells_out"])
        self.assertEqual(row["lec"], ["6_final:IDENTICAL"])
        self.assertIsNone(row["sha256"]["6_final.odb"])                     # not fetched back: stays on the host
        self.assertEqual(collect.collect_row(os.path.join(FIX, "add_rerun"), "add_3f31f3f29548__min_s2")["status"],
                         "pending")

    def test_metric_texts_are_kept_as_text(self):
        """ORFS's report numbers are kept as their JSON text (never floats): 6_report.json, 6_finish.rpt and
        5_2_route.json written here from the stored row's own texts come back as the same strings."""
        with open(os.path.join(EXJOB_DIR, "rows", EXJOB + ".json"), encoding="utf-8") as fh:
            stored = json.load(fh)
        d = os.path.join(self.tmp, "job")
        w = pnr.work_dirs(d, EXJOB)
        for x in w.values():
            os.makedirs(x)
        os.makedirs(os.path.join(d, "logs"))
        with open(os.path.join(d, "logs", "status.txt"), "w") as fh:
            fh.write(f"{EXJOB} rc=0 seconds=66.4351 cpus=0-1 date=2026-11-13\n")
        with open(os.path.join(w["logs"], "6_report.json"), "w") as fh:
            fh.write("{" + ", ".join(f'"{k}": {v}' for k, v in stored["metrics"].items()) + ', "other": 1}')
        with open(os.path.join(w["reports"], "6_finish.rpt"), "w") as fh:
            fh.write(f"period_min = {stored['period_min'][0]} fmax = 40.2\n")
        with open(os.path.join(w["logs"], "5_2_route.json"), "w") as fh:
            fh.write('{"detailedroute__route__drc_errors": 0, "detailedroute__route__wirelength": 67}')
        row = collect.collect_row(d, EXJOB)
        self.assertEqual(row["metrics"], stored["metrics"])
        self.assertEqual((row["period_min"], row["drc"], row["route_wirelength"]), (["24.85"], 0, "67"))

    def test_the_spef_hash_drops_its_tool_lines(self):
        a = os.path.join(self.tmp, "a.spef")
        b = os.path.join(self.tmp, "b.spef")
        body = b'*SPEF "IEEE 1481-1998"\n*DESIGN "band"\n*D_NET x 1\n*END\n'
        write(a, b'*DATE "Fri Nov 13 08:52:00 2026"\n*VENDOR "a"\n*PROGRAM "b"\n*VERSION "1"\n' + body)
        write(b, b'*DATE "Sat Nov 14 01:00:00 2026"\n*VENDOR "a"\n*PROGRAM "b"\n*VERSION "2"\n' + body)
        self.assertEqual(collect.spef_sha256(a), collect.spef_sha256(b))
        write(b, b'*DATE "x"\n' + body.replace(b"x 1", b"x 2"))
        self.assertNotEqual(collect.spef_sha256(a), collect.spef_sha256(b))

    @unittest.skipUnless(liberty_present(), "the pinned ASAP7 liberty is not here (score/ppa.py --pdk asap7 "
                                            "--fetch-liberty)")
    def test_the_fixture_cell_area_is_the_liberty_s(self):
        self.assertEqual(collect.liberty_areas()["AND2x2_ASAP7_75t_R"], AND2_AREA)
        self.assertEqual(check_sitedata.liberty_area_reader()("AND2x2_ASAP7_75t_R"), AND2_AREA)

    @unittest.skipUnless(encoder_matches(), "Pillow 11.1.0 with libwebp 1.5.0 not installed: the encoder's bytes "
                                            "depend on them")
    def test_the_encoder_makes_the_committed_pictures(self):
        e = lb.asap7pnr_entry(committed("_example")[1], BAND_LP)
        pic, thumb, rec = encode.encode(read(os.path.join(EXJOB_DIR, "img", EXJOB + ".png"), "rb"))
        L = e["layout"]
        self.assertEqual((rec["sha256"], rec["thumb_sha256"], rec["quality"], rec["px"], rec["png_sha256"]),
                         (L["image_sha256"], L["thumb_sha256"], L["webp_quality"], L["image_px"], L["render_png_sha256"]))
        self.assertEqual(pic, read(os.path.join(SVGOLF, *L["image"].split("/")), "rb"))

    def test_the_whole_path_reproduces_the_committed_table(self):
        """render -> picture -> entry -> site data -> `asap7pnr --import`: the committed _example.json, byte for byte,
        and its four picture files, from the stored job of band_lp (the table as it was before that run: the design's
        entry pending with its request)."""
        text, table = committed("_example")
        out = os.path.join(self.tmp, "out")
        e, view = collected_entry(out, table)
        want = copy.deepcopy(lb.asap7pnr_entry(table, BAND_LP))
        want["layout"] = tree_layout_to_images(want["layout"])
        self.assertEqual(e, want)
        collect.sitedata("_example", out, [e], table=pending_tree(table, BAND_LP), view=view)
        data, pictures, dropped, bad = lb.asap7pnr_import(out, "_example", designs_of("_example"))
        self.assertEqual((bad, dropped), ([], []))
        self.assertEqual(json.dumps(data, indent=1, sort_keys=True) + "\n", text)
        for rel, blob in pictures.items():
            self.assertEqual(blob, read(os.path.join(SVGOLF, *rel.split("/")), "rb"), rel)
        # against the tree as it is (the design already routed), the same entry is accepted, a changed one is not
        collect.sitedata("_example", out, [e], table=table, view=view)
        e2 = copy.deepcopy(e)
        e2["runs"][0]["seconds"] = 1.0
        with self.assertRaises(collect.CollectError):
            collect.sitedata("_example", out, [e2], table=table, view=view)

    def test_the_entry_refuses_what_is_not_the_design_s_scoring_run(self):
        table = committed("_example")[1]
        out = os.path.join(self.tmp, "out")
        rq = copy.deepcopy(lb.asap7pnr_entry(table, BAND_LP)["request"])
        mk = read(os.path.join(EXJOB_DIR, "cfg", EXJOB + ".mk"), "rb")
        sdc = read(os.path.join(EXJOB_DIR, "sdc", EXNICK + ".sdc"), "rb")
        row = json.loads(read(os.path.join(EXJOB_DIR, "rows", EXJOB + ".json")))
        for name, over in (("another seed asked", {"request": dict(rq, seed=7, source="record")}),
                           ("a config.mk under other pins", {"mk_bytes": mk.replace(b"0.60", b"0.70")}),
                           ("another period", {"sdc_bytes": sdc.replace(b"-period 56.0", b"-period 57.0")}),
                           ("another placed netlist",
                            {"row": dict(row, sha256=dict(row["sha256"], **{"1_2_yosys.v": "0" * 64}))}),
                           ("a cell outside the liberty", {"areas": {}})):
            with self.subTest(name), self.assertRaises(collect.CollectError):
                collected_entry(out, table, **over)

    def test_a_failed_run(self):
        table = committed("_example")[1]
        row = json.loads(read(os.path.join(EXJOB_DIR, "rows", EXJOB + ".json")))
        for bad in ({"drc": 3}, {"lec": ["6_final:UNKNOWN"]}, {"lec": []}, {"rc": 2, "status": "failed"}):
            with self.subTest(bad=bad):
                e, _ = collected_entry(os.path.join(self.tmp, "out"), table, row=dict(row, **bad))
                self.assertEqual((e["status"], e["layout"], e["scores"]["v_owner"], e["runs"][0]["status"]),
                                 ("failed", None, None, "failed"))
                self.assertIn("error", e["runs"][0])


class SitedataCheckTest(TempDir):
    def setUp(self):
        super().setUp()
        self.text, self.table = committed("_example")
        self.tree = pending_tree(self.table, BAND_LP)
        self.out = os.path.join(self.tmp, "out")
        self.entry, self.view = collected_entry(self.out, self.table)
        collect.sitedata("_example", self.out, [self.entry], table=self.tree, view=self.view)
        self.path = os.path.join(self.out, "sitedata", "_example.json")

    def check(self, tree=None):
        return check_sitedata.check(self.out, "_example", [EXJOB_DIR], area_of=area_of(),
                                    tree=self.tree if tree is None else tree)

    def edit(self, fn):
        data = json.loads(read(self.path))
        fn(data, lb.asap7pnr_entry(data, BAND_LP))
        with open(self.path, "w") as fh:
            fh.write(json.dumps(data, indent=1, sort_keys=True) + "\n")

    def test_clean(self):
        problems, notes = self.check()
        self.assertEqual(problems, [])
        self.assertEqual(len(notes), 0 if encoder_matches() else 1)
        self.assertEqual(check_sitedata.check(self.out, "_example", [EXJOB_DIR], area_of=area_of())[0], [])

    def test_planted_faults_are_caught(self):
        """Each fault in a fresh copy of the collected data; each must be a problem."""
        good = read(self.path)

        def area_plus_one(d, e):
            r = e["runs"][0]
            r["area_e5um2"] += 1
            r["exact"] = r["area_e5um2"] * r["time_ps"]
            e["scores"]["v_owner"].update(area_e5um2=r["area_e5um2"], exact=r["exact"], um2ns=r["exact"] / 1e8)

        def other_config(d, e):
            e["runs"][0]["config_mk_sha256"] = "e79fc6784d9ad293374b38bfe851d693ad4cb299104822f4a7451f489bf6094b"

        def other_odb(d, e):
            e["runs"][0]["artifacts"]["6_final.odb"] = "1" * 64
            e["layout"]["odb_sha256"] = "1" * 64

        def other_request(d, e):
            e["request"].update(seed=1, source="record")

        def other_delay(d, e):
            r = e["runs"][0]
            r["delay_ps"] += 0
            r["orfs"]["setup_ws"] = "31.6541"

        def carried_changed(d, e):
            d["designs"][0]["runs"][1]["seconds"] = 1.0

        def a_design_not_shown(d, e):
            x = copy.deepcopy(e)
            x["sv_sha256"] = "f" * 64
            d["designs"].append(x)

        def other_die(d, e):
            e["layout"]["die_um"] = ["3.88", "3.87"]

        for name, fn in (("area + 1, product consistent", area_plus_one), ("another job's config.mk", other_config),
                         ("another 6_final.odb", other_odb), ("a request the tree does not store", other_request),
                         ("raw slack not the row's", other_delay), ("a carried entry changed", carried_changed),
                         ("an entry for a design the task does not show", a_design_not_shown),
                         ("another die box", other_die)):
            with self.subTest(name):
                with open(self.path, "w") as fh:
                    fh.write(good)
                self.edit(fn)
                self.assertNotEqual(self.check()[0], [], name)
        with open(self.path, "w") as fh:
            fh.write(good)
        no_request = copy.deepcopy(self.tree)
        no_request["designs"] = [x for x in no_request["designs"] if x["sv_sha256"] != BAND_LP]
        self.assertTrue(any("stores no request" in p for p in self.check(tree=no_request)[0]))

    @unittest.skipUnless(encoder_matches(), "Pillow 11.1.0 with libwebp 1.5.0 not installed")
    def test_a_picture_that_is_not_the_render(self):
        other = read(os.path.join(SVGOLF, "site", "layouts", "add",
                                  sorted(f for f in os.listdir(os.path.join(SVGOLF, "site", "layouts", "add"))
                                         if f.endswith(".thumb.webp"))[0]), "rb")
        p = os.path.join(self.out, "images", "_example", BAND_LP[:16] + ".thumb.webp")
        with open(p, "wb") as fh:
            fh.write(other)

        def follow(d, e):
            e["layout"].update(thumb_sha256=pnr.sha256_bytes(other), thumb_bytes=len(other),
                               thumb_px=list(lb.webp_size(other)))
        self.edit(follow)
        self.assertTrue(any("not the render encoded" in x for x in self.check()[0]))

    @unittest.skipUnless(encoder_matches(), "Pillow 11.1.0 with libwebp 1.5.0 not installed")
    def test_a_thumbnail_encoded_again_one_step_away(self):
        """A thumbnail encoded again from the same render at quality 79 (as the campaigns did for the publication
        scan; the entry records no thumbnail quality) is the render's: a note, not a problem. At quality 49, outside
        the encoder's ladder, it is a problem."""
        import io
        from PIL import Image
        im = Image.open(io.BytesIO(read(os.path.join(EXJOB_DIR, "img", EXJOB + ".png"), "rb"))).convert("RGB")
        p = os.path.join(self.out, "images", "_example", BAND_LP[:16] + ".thumb.webp")
        for q, ok in ((79, True), (49, False)):
            with self.subTest(quality=q):
                buf = io.BytesIO()
                im.resize((640, 640), Image.Resampling.LANCZOS).save(buf, format="WEBP", quality=q, method=6, exact=False)
                write(p, buf.getvalue())

                def follow(d, e, b=buf.getvalue()):
                    e["layout"].update(thumb_sha256=pnr.sha256_bytes(b), thumb_bytes=len(b))
                self.edit(follow)
                problems, notes = self.check()
                if ok:
                    self.assertEqual(problems, [])
                    self.assertTrue(any("quality 79, not 80" in n for n in notes), notes)
                else:
                    self.assertTrue(any("not the render encoded" in x for x in problems), problems)

    def test_the_command(self):
        if not liberty_present():
            self.assertEqual(check_sitedata.main([self.out, "--jobs", EXJOB_DIR, "--liberty",
                                                  os.path.join(self.tmp, "nowhere")]), 2)
            self.skipTest("the pinned ASAP7 liberty is not here: the command's exit status 2 checked")
        # the tree's own table (the design already routed): the collected entry is that entry, so it passes too
        self.assertEqual(check_sitedata.main([self.out, "--jobs", EXJOB_DIR]), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
