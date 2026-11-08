#!/usr/bin/env python3.12
"""The `--ppa` wiring of check.py (WP-X3), without Lean: check.py's real stages (source, extract, banlist, fourstate,
score, postsynth, ppa) run on reference designs (pyslang, the extractor, Yosys, Verilator), and the Lean runner is a fake
whose `compile` of the generated `Submission.Design` answers what Lean would (the stage is untouched by the wiring).

  * `--ppa off`: the result is, character for character, the baseline checker's (the commit before the wiring) on the
    `add` and `aes_sbox` references, with only the machine- and run-dependent leaves masked (tests/checker/byte_identity.py,
    goldens in tests/checker/ppa_wiring/);
  * `--ppa auto` (the default) is that result plus EXACTLY the key `ppa` and the stage `stages.ppa`;
  * the liberty absent (`SVGOLF_SKY130_LIB` at a missing file), or not the pinned file: `auto` records
    `ppa: {"available": false, "reason": ...}` with one stderr line and changes nothing else; `require` is an
    infrastructure error before any other work (exit status 2);
  * a design the pinned flow cannot weigh carries its loud reason and never fails the check, in every mode;
  * the weighed netlist IS the one the postsynth stage simulated (`netlist_sha256` equal, no second synthesis);
  * the integrity tripwire fingerprints score/ppa.py, score/ppa_pins.json and flow A1''s score/ppa_mapped.ys and
    score/ppa_mapped_pins.json by content and catches an edit of any;
  * WP-X4, flow A1': a weighed `ppa` block carries the sub-object `mapped` (a real `abc -liberty` mapping of the canonical
    RTLIL of the same score run), equal to the goldens of score/tests/ppa/expected_ppa_mapped.json; the rest of `ppa` is what
    it was; a design the mapping cannot weigh has `mapped: {available: false, reason}` and the check goes on, in `auto` and
    `require` alike; a mapped netlist that is not the scored circuit, or a defect of ppa.py, is an infrastructure error in
    `require` only; a canonical RTLIL changed between the stages is an infrastructure error in every mode; `--ppa off` never
    maps.

The real-liberty tests are SKIPPED where the pinned liberty is absent (`python3.12 score/ppa.py --fetch-liberty`);
SVGOLF_PPA_REQUIRE_LIB=1 turns that into a failure (tests/run.py sets it when the file exists).

    python3.12 tests/checker/test_ppa_wiring.py
    UPDATE_GOLDEN=1 python3.12 tests/checker/test_ppa_wiring.py   # re-record the goldens (see PROVENANCE.txt)
"""

import contextlib
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import byte_identity as bi  # noqa: E402
import ppa  # noqa: E402
import postsynth  # noqa: E402


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


checkpy = load("svgolf_check_py_ppa_wiring", os.path.join(SVGOLF, "check.py"))
PY = sys.executable
REAL_LIB = ppa.find_liberty(None, ppa.Pins())
HAVE_LIB = os.path.isfile(REAL_LIB)
REQUIRE_LIB = os.environ.get("SVGOLF_PPA_REQUIRE_LIB") == "1"
UPDATE = os.environ.get("UPDATE_GOLDEN") == "1"


def have_flow():
    import score
    if shutil.which(score.yosys_bin()) is None or shutil.which("verilator") is None:
        return False
    try:
        import pyslang  # noqa: F401
    except ImportError:
        return False
    return True


needs_flow = unittest.skipUnless(have_flow(), "needs Yosys, pyslang and Verilator")
needs_lib = unittest.skipUnless(HAVE_LIB, f"the pinned sky130 liberty is absent ({REAL_LIB}); run "
                                          "`python3.12 score/ppa.py --fetch-liberty`")

TASKS = {"add": ("add", "add_n"), "aes_sbox": ("aes_sbox", "sbox_bp")}


class FakeLean:
    """Stands in for check.py's `Lean`: `compile` answers the marker line the real design stage prints."""
    free_points = 1
    compiled = 0

    def __init__(self, stage, wrap):
        self.stage, self.wrap = stage, wrap

    def run(self, args, timeout=None, lake_env=True, **kw):
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        FakeLean.compiled += 1
        return 0, f"SVGOLF_UNSUPPORTED_FREE {FakeLean.free_points}\n", 1.0


_RUNS = {}


def _no_patch():
    return contextlib.nullcontext()


# failures of flow A1' injected into `ppa` (names for `run_check(patch=...)`)
PATCHES = {
    None: _no_patch,
    "mapfail": lambda: mock.patch.object(ppa, "map_rtlil", side_effect=ppa.PpaError("the mapping run failed: boom\n  detail")),
    "defect": lambda: mock.patch.object(ppa, "check_equivalent", side_effect=ppa.MappedDefect("differs at y[0] on vector 3")),
    "boom": lambda: mock.patch.object(ppa, "map_rtlil", side_effect=ValueError("boom")),
    # sky130_a0_v2: the repaired netlist is electrically illegal (the design's fault: the stage rejects it)
    "illegal": lambda: mock.patch.object(ppa, "analyze", side_effect=ppa.IllegalNetlist(
        "the sky130 netlist is electrically illegal and the repair (buffer trees, replicated tie cells) cannot make it "
        "legal: the net n (inv_1 g7), driving 99 cell pins: its driver may carry at most 0.0 fF, less than the buffers it "
        "would need. The ranked sky130 score (sky130_a0_v2) is taken on a legal netlist only (no timing table is "
        "extrapolated), so the design is rejected", {"over_max_capacitance": 1})),
}


def run_check(task, ppa_mode, lib=None, tamper=False, design=None, patch=None):
    """check.py's `check()` on the task's reference, `--unproved --postsynth full --no-trusted-build` (the baseline
    goldens' command), with the fake Lean. `lib`: value of $SVGOLF_SKY130_LIB (None: the environment as it is).
    Returns (result, stderr text). A run is a function of its arguments, so it is made once per module (a run costs the
    Verilator build of the postsynth stage, 2 to 4 s) and its staging and work directories are kept until the
    module ends. `tamper`: the netlist file (`tamper="rtlil"`: the canonical RTLIL the mapping reads) is changed after the
    postsynth stage has verified it (a surviving process of the proof build, say). `design`: another .sv than the task's
    reference. `patch`: a name of PATCHES, a failure of flow A1' injected into `ppa` for the run."""
    key = (task, ppa_mode, lib, tamper, design, patch)
    if key not in _RUNS:
        tdir = os.path.join(SVGOLF, "tasks", task)
        stem = TASKS[task][1]
        with open(os.path.join(tdir, "task.json")) as fh:
            FakeLean.free_points = len(checkpy.unsupported_check_points(json.load(fh)))
        FakeLean.compiled = 0
        stage = tempfile.mkdtemp(prefix="svgolf-ppawiring-")
        err = io.StringIO()
        env = {} if lib is None else {"SVGOLF_SKY130_LIB": lib}
        orig = checkpy.Lean
        checkpy.Lean = FakeLean
        real_run = postsynth.run

        def swapping_run(*a, **kw):
            rec = real_run(*a, **kw)
            # a[3]: the netlist path, a[5]: the work directory (postsynth.run(task, sv, env_path, netlist, sres, work, ...))
            with open(a[3] if tamper is True else os.path.join(a[5], "canon.il"), "a") as fh:
                fh.write("\n// swapped after postsynth\n" if tamper is True else "\n# swapped after postsynth\n")
            return rec
        try:
            with mock.patch.dict(os.environ, env), contextlib.redirect_stderr(err), \
                    mock.patch.object(postsynth, "run", swapping_run if tamper else real_run), \
                    PATCHES[patch]():
                res = checkpy.check(tdir, design or os.path.join(tdir, "reference", stem + ".sv"), None, stage, [],
                                    do_score=True, build_trusted=False, unproved=True, keep=True,
                                    postsynth_mode="full", ppa_mode=ppa_mode)
        finally:
            checkpy.Lean = orig
        _RUNS[key] = (res, err.getvalue())
    return _RUNS[key]


def tearDownModule():
    for res, _ in _RUNS.values():
        for k in ("stage_dir", "postsynth_dir"):
            if res.get(k):
                shutil.rmtree(res[k], ignore_errors=True)


def checkpy_run_off():
    """An `off` run with the liberty opener patched to fail (not cached: the patch is the point)."""
    tdir = os.path.join(SVGOLF, "tasks", "_example")
    stage = tempfile.mkdtemp(prefix="svgolf-ppawiring-")
    err = io.StringIO()
    orig = checkpy.Lean
    checkpy.Lean = FakeLean
    FakeLean.free_points = 4
    try:
        with contextlib.redirect_stderr(err):
            res = checkpy.check(tdir, os.path.join(tdir, "reference", "band.sv"), None, stage, [], do_score=True,
                                build_trusted=False, unproved=True, postsynth_mode="light", ppa_mode="off")
    finally:
        checkpy.Lean = orig
        shutil.rmtree(stage, ignore_errors=True)
    return res, err.getvalue()


def bare(res):
    """`res` without `postsynth_dir`, which only a `keep` run has (the runs here keep their directories until the
    module ends; the goldens are of runs without `--keep`)."""
    return {k: v for k, v in res.items() if k != "postsynth_dir"}


def missing_lib():
    return os.path.join(tempfile.gettempdir(), "svgolf-no-such-dir", "sky130_missing.lib")


class Tmp(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="svgolf-ppawiring-t-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)


@needs_flow
class ByteIdentity(unittest.TestCase):
    """(c) of WP-X3: `--ppa off` equals the baseline checker's result; `--ppa auto` equals it plus the new key and
    stage, and nothing else. The baseline is the commit before the wiring (goldens: tests/checker/ppa_wiring/)."""

    def test_off_equals_the_baseline_and_has_no_ppa_trace(self):
        for task in TASKS:
            with self.subTest(task=task):
                res, err = run_check(task, "off", lib=missing_lib())      # `off` never looks at the liberty
                self.assertNotIn("ppa", res)
                self.assertNotIn("ppa", res["stages"])
                self.assertNotIn("ppa", err)
                if UPDATE:
                    with open(bi.golden_path(task, "unproved"), "w") as fh:
                        fh.write(bi.render(bare(res)))
                self.assertEqual(bi.render(bare(res)), bi.golden(task, "unproved"))

    def test_auto_is_off_plus_exactly_the_key_and_the_stage(self):
        for task in TASKS:
            with self.subTest(task=task):
                off, _ = run_check(task, "off", lib=missing_lib())
                auto, err = run_check(task, "auto")
                self.assertEqual(set(auto) - set(off), {"ppa"})
                self.assertEqual(set(auto["stages"]) - set(off["stages"]), {"ppa"})
                self.assertEqual(set(off) - set(auto), set())
                # everything else, character for character
                # (two results of one checkout: only times and directories are masked, the build identities must agree)
                self.assertEqual(bi.render(bi.without_ppa(bare(auto)), strict=True), bi.render(bare(off), strict=True))
                self.assertEqual(bi.render(bi.without_ppa(bare(auto))), bi.golden(task, "unproved"))
                self.assertEqual(auto["stages"]["ppa"]["mode"], "auto")
                self.assertIsInstance(auto["stages"]["ppa"]["seconds"], float)
                self.assertEqual(auto["stage"], "unproved")        # the stage never changes the verdict
                if HAVE_LIB:
                    self.assertTrue(auto["ppa"]["available"], auto["ppa"])
                    self.assertIn("ppa: ", err)
                else:
                    self.assertEqual(auto["ppa"]["available"], False)
                    self.assertIn("ppa: not computed", err)

    def test_the_default_board_is_the_same_with_the_columns_present(self):
        off, _ = run_check("add", "off", lib=missing_lib())
        auto, _ = run_check("add", "auto")
        self.assertEqual(auto["score"], off["score"])
        self.assertEqual((auto["score"]["area_ge"], auto["score"]["depth"]), (112.0, 33))

    def test_a_clean_unproved_run_has_its_sentence_as_a_note(self):
        """The shared contract (the 11/05 newcomer study): `accepted` false, stage `unproved`, `errors` empty, the
        sentence in `notes`, `unproved_ok` true (and check.py's main exits 0 on it)."""
        res, err = run_check("add", "off", lib=missing_lib())
        self.assertEqual((res["accepted"], res["stage"], res["errors"], res["unproved_ok"]), (False, "unproved", [], True))
        self.assertTrue(res["notes"][0].startswith("--unproved: every check that needs no proof passed"))
        # the long stages say when they start (shared contract item 3), and never mention the columns under --ppa off
        for s in ("extract", "score", "postsynth"):
            self.assertIn(f"check: {s} ...", err)

    def test_the_wrappers_keys_are_the_machines_not_the_checks(self):
        """`without_ppa` strips what a Lean slot wrapper adds (`waited` per stage, `lean_wrap`), as it strips the
        sandbox's: the comparison against the goldens must not depend on whether a wrapper ran."""
        res = {"accepted": True, "lean_wrap": {"once": True, "waited": 3.0},
               "stages": {"design": {"exit": 0, "seconds": 1.0, "waited": 30.5}, "solution": {"exit": 0}}}
        self.assertEqual(bi.without_ppa(res), {"accepted": True, "stages": {"design": {"exit": 0, "seconds": 1.0},
                                                                           "solution": {"exit": 0}}})

    def test_the_solutions_progress_record_is_this_runs(self):
        """`without_ppa` strips the solution's `progress` record (when each declaration finished: this run's times)."""
        res = {"accepted": True, "stages": {"solution": {"exit": 0, "progress": {"finished": 3, "run_s": 2.0,
                                                                                  "last": None, "slowest": []}}}}
        self.assertEqual(bi.without_ppa(res), {"accepted": True, "stages": {"solution": {"exit": 0}}})


@needs_flow
class AbsentLiberty(unittest.TestCase):
    """(b) of WP-X3: the modes, with `SVGOLF_SKY130_LIB` pointing at a file that does not exist."""

    def test_auto_records_why_and_changes_nothing_else(self):
        off, _ = run_check("add", "off", lib=missing_lib())
        auto, err = run_check("add", "auto", lib=missing_lib())
        self.assertEqual(set(auto["ppa"]), {"available", "reason"})
        self.assertFalse(auto["ppa"]["available"])
        self.assertIn("liberty not found", auto["ppa"]["reason"])
        self.assertIn("--fetch-liberty", auto["ppa"]["reason"])
        self.assertNotIn("\n", auto["ppa"]["reason"])
        self.assertEqual(auto["stages"]["ppa"]["mode"], "auto")
        self.assertEqual(bi.render(bi.without_ppa(bare(auto)), strict=True), bi.render(bare(off), strict=True))
        lines = [ln for ln in err.splitlines() if ln.startswith("ppa:")]
        self.assertEqual(len(lines), 1)
        self.assertIn("not computed: liberty not found", lines[0])

    def test_off_never_looks_at_the_liberty(self):
        with mock.patch.object(ppa, "open_library", side_effect=AssertionError("off opened the liberty")):
            res, err = checkpy_run_off()
        self.assertNotIn("ppa", res)
        self.assertNotIn("ppa", err)

    def test_require_is_an_infrastructure_error_before_any_work(self):
        FakeLean.compiled = 0
        with self.assertRaises(RuntimeError) as cm:
            run_check("add", "require", lib=missing_lib())
        self.assertIn("ppa: liberty not found", str(cm.exception))
        self.assertEqual(FakeLean.compiled, 0)             # not even the design stage ran

    def test_require_exit_status_is_2_and_the_json_says_infrastructure(self):
        env = dict(os.environ, SVGOLF_SKY130_LIB=missing_lib())
        tdir = os.path.join(SVGOLF, "tasks", "add")
        proc = subprocess.run([PY, os.path.join(SVGOLF, "check.py"), tdir,
                               os.path.join(tdir, "reference", "add_n.sv"), "--unproved",
                               "--ppa", "require"], capture_output=True, text=True, env=env, cwd=SVGOLF)
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        out = json.loads(proc.stdout)
        self.assertEqual((out["accepted"], out["stage"]), (False, "infrastructure"))
        self.assertIn("ppa: liberty not found", out["errors"][0])

    def test_a_file_that_is_not_the_pinned_liberty_is_not_used(self):
        with tempfile.TemporaryDirectory() as d:
            fake = os.path.join(d, "other.lib")
            with open(fake, "w") as fh:
                fh.write('library ("not the pinned file") { }\n')
            net = os.path.join(d, "netlist.v")
            with open(net, "w") as fh:
                fh.write(PpaBlock.TINY)
            with mock.patch.dict(os.environ, {"SVGOLF_SKY130_LIB": fake}):
                b = checkpy.ppa_block(net, {"depth": 1, "num_gates": 1}, "auto")
                self.assertFalse(b["available"])
                self.assertIn("is not the pinned", b["reason"])
                with self.assertRaises(RuntimeError) as cm:      # and `require` stops before any work
                    run_check("add", "require", lib=fake)
                self.assertIn("is not the pinned", str(cm.exception))

    def test_bad_mode_is_an_error(self):
        with self.assertRaises(RuntimeError):
            run_check("add", "sometimes")
        proc = subprocess.run([PY, os.path.join(SVGOLF, "check.py"), "x", "y", "--ppa", "sometimes"],
                              capture_output=True, text=True, cwd=SVGOLF)
        self.assertEqual(proc.returncode, 2)
        self.assertIn("invalid choice", proc.stderr)


@unittest.skipIf(not hasattr(os, "geteuid") or os.geteuid() == 0, "root reads a mode-000 file")
class UnreadableLiberty(Tmp):
    """A liberty file that exists but cannot be read (permissions) is an absent one: never a traceback, never exit status 1
    (check.py's `rejected`), never a reason to fail a check (review of WP-X3)."""

    def locked(self):
        p = os.path.join(self.tmp, "locked.lib")
        open(p, "w").close()      # the contents do not matter: the open() fails first
        os.chmod(p, 0)
        self.addCleanup(os.chmod, p, 0o600)
        return p

    def test_ppa_block_says_why_in_auto_and_is_an_infrastructure_error_in_require(self):
        net = os.path.join(self.tmp, "netlist.v")
        with open(net, "w") as fh:
            fh.write(PpaBlock.TINY)
        with mock.patch.dict(os.environ, {"SVGOLF_SKY130_LIB": self.locked()}):
            b = checkpy.ppa_block(net, {"depth": 1, "num_gates": 1}, "auto")
            self.assertEqual(set(b), {"available", "reason"})
            self.assertFalse(b["available"])
            self.assertIn("cannot be read", b["reason"])
            with self.assertRaises(RuntimeError) as cm:
                checkpy.ppa_block(net, {"depth": 1, "num_gates": 1}, "require")
            self.assertIn("ppa: ", str(cm.exception))
            self.assertIn("cannot be read", str(cm.exception))

    def test_require_exit_status_is_2_with_the_json(self):
        env = dict(os.environ, SVGOLF_SKY130_LIB=self.locked())
        tdir = os.path.join(SVGOLF, "tasks", "add")
        proc = subprocess.run([PY, os.path.join(SVGOLF, "check.py"), tdir, os.path.join(tdir, "reference", "add_n.sv"),
                               "--unproved", "--ppa", "require"], capture_output=True, text=True, env=env, cwd=SVGOLF)
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        self.assertNotIn("Traceback", proc.stderr)
        out = json.loads(proc.stdout)
        self.assertEqual((out["accepted"], out["stage"]), (False, "infrastructure"))
        self.assertIn("cannot be read", out["errors"][0])

    @needs_flow
    def test_an_auto_check_completes_and_records_the_reason(self):
        off, _ = run_check("add", "off", lib=missing_lib())
        auto, err = run_check("add", "auto", lib=self.locked())
        self.assertEqual(auto["stage"], "unproved")
        self.assertEqual(set(auto["ppa"]), {"available", "reason"})
        self.assertIn("cannot be read", auto["ppa"]["reason"])
        self.assertEqual(bi.render(bi.without_ppa(bare(auto)), strict=True), bi.render(bare(off), strict=True))
        self.assertEqual(len([ln for ln in err.splitlines() if ln.startswith("ppa:")]), 1)


class PpaBlock(Tmp):
    """`ppa_block`, the function behind the stage, on a tiny netlist (no flow needed)."""
    TINY = ("module tiny(a, b, y);\n  input a;\n  input b;\n  output y;\n"
            "  \\$_AND_  _1_ (\n    .A(a),\n    .B(b),\n    .Y(y)\n  );\nendmodule\n")

    def netlist(self, text=None):
        p = os.path.join(self.tmp, "netlist.v")
        with open(p, "w") as fh:
            fh.write(self.TINY if text is None else text)
        return p

    def test_a_netlist_the_flow_cannot_weigh_carries_its_reason_in_every_mode(self):
        # (a latch: the flow weighs gates and the clocked flow's $_DFF_P_ flop, nothing else)
        flop = self.TINY.replace("\\$_AND_ ", "\\$_DLATCH_P_").replace(".A(a)", ".E(a)").replace(".B(b)", ".D(b)")
        sres = {"depth": 1, "num_gates": 1}
        with mock.patch.object(ppa, "open_library", return_value=(mock.Mock(), ppa.Pins())):
            for mode in ("auto", "require"):
                b = checkpy.ppa_block(self.netlist(flop), sres, mode)
                self.assertEqual(set(b), {"available", "reason"})
                self.assertFalse(b["available"])
                self.assertIn("outside the A0' table", b["reason"])

    def test_a_defect_of_ppa_py_does_not_fail_the_check(self):
        sres = {"depth": 1, "num_gates": 1}
        with mock.patch.object(ppa, "open_library", return_value=(mock.Mock(), ppa.Pins())), \
                mock.patch.object(ppa, "analyze", side_effect=ValueError("boom")):
            b = checkpy.ppa_block(self.netlist(), sres, "auto")
            self.assertEqual(b, {"available": False,
                                 "reason": "ppa.py failed on this netlist: ValueError: boom"})
            with self.assertRaises(RuntimeError) as cm:        # under `require` a defect is an infrastructure error
                checkpy.ppa_block(self.netlist(), sres, "require")
            self.assertIn("ppa.py failed on this netlist", str(cm.exception))

    def test_the_weighed_file_must_be_the_verified_one(self):
        """`expect_sha256` (the postsynth stage's `netlist_sha256`): a file that is not those bytes is an integrity
        failure in EVERY mode (the number would be the number of a netlist nobody simulated), not a property of the design."""
        sres = {"depth": 1, "num_gates": 1}
        path = self.netlist()
        with open(path, "rb") as fh:
            verified = ppa.sha256_bytes(fh.read())
        swapped = self.TINY.replace("\\$_AND_ ", "\\$_NAND_")        # another valid, weighable netlist
        self.assertNotEqual(ppa.sha256_bytes(swapped.encode()), verified)
        with mock.patch.object(ppa, "open_library", return_value=(mock.Mock(), ppa.Pins())):
            for mode in ("auto", "require"):
                with self.assertRaises(RuntimeError, msg=mode) as cm:
                    checkpy.ppa_block(self.netlist(swapped), sres, mode, expect_sha256=verified)
                self.assertIn("is not the one the postsynth stage verified", str(cm.exception))
                self.assertIn(verified, str(cm.exception))

    @needs_lib
    def test_the_verified_file_is_weighed_and_its_hash_is_the_recorded_one(self):
        sres = {"depth": 1, "num_gates": 1}
        path = self.netlist()
        with open(path, "rb") as fh:
            verified = ppa.sha256_bytes(fh.read())
        b = checkpy.ppa_block(path, sres, "require", expect_sha256=verified)
        self.assertTrue(b["available"])
        self.assertEqual(b["netlist_sha256"], verified)
        self.assertEqual(b, checkpy.ppa_block(path, sres, "require"))      # None: not checked, same block

    @needs_lib
    def test_weighed_block_has_the_columns_and_the_flag(self):
        b = checkpy.ppa_block(self.netlist(), {"depth": 1, "num_gates": 1}, "auto")
        self.assertTrue(b["available"])
        # sky130_a0_v2: the repair buffers only what is over a limit; the one and2_1 (6.256 um^2) is not
        self.assertEqual((b["area_e4um2_sky130"], b["unit_depth"], b["cells_sky130"]), (62560, 1, 1))
        self.assertEqual((b["cell_hist_sky130"], b["repair"]["cells_before"], b["repair"]["buffers"]), ({"and2_1": 1}, 1, 0))
        self.assertEqual(b["ppa_version"], ppa.Pins().version)
        self.assertEqual(set(b), {"available", *ppa.weigh_netlist_file(self.netlist())})
        again = checkpy.ppa_block(self.netlist(), {"depth": 1, "num_gates": 1}, "require")
        self.assertEqual(b, again)

    BROADCAST = ("module bc(a, b, y, z);\n  input a;\n  input b;\n  output [19:0] y;\n  output z;\n"
                 "  \\$_NOT_  _1_ (\n    .A(b),\n    .Y(z)\n  );\n  assign y = {" + ", ".join(["a"] * 20) + "};\nendmodule\n")

    @needs_lib
    def test_a_broadcast_input_is_buffered_not_rejected(self):
        """sky130_a0_v2 (buffering only): the input `a` wired to 20 output bits (200 fF on its buf_1 driver, max_capacitance
        130 fF) is buffered (one buf_2) and weighed; the ABC-sizing repair never saw that net and rejected the design.
        sky130_a0_v3: the drive is the TASK's (`input_drive`): a task declaring buf_1 gets that tree, a task declaring none
        the default buf_8, under which 200 fF is within limits and nothing is buffered; the block's `setup` says which."""
        net, sres = self.netlist(self.BROADCAST), {"depth": 1, "num_gates": 1}
        b1 = ppa.Pins().prefix + "buf_1"
        b = checkpy.ppa_block(net, sres, "require", task={"name": "t", "input_drive": b1})
        self.assertTrue(b["available"], b)
        self.assertEqual((b["cell_hist_sky130"], b["repair"]["buffers"], b["legality"]["over_max_capacitance"],
                          b["setup"]["input_drive"]), ({"buf_2": 1, "inv_1": 1}, 1, 0, b1))
        b = checkpy.ppa_block(net, sres, "require", task={"name": "t"})
        self.assertEqual((b["cell_hist_sky130"], b["repair"]["buffers"], b["setup"]["input_drive"]),
                         ({"inv_1": 1}, 0, ppa.Pins().input_drive_default))

    @needs_lib
    def test_an_unknown_input_drive_is_a_task_configuration_error(self):
        """A task.json `input_drive` outside the pins' allowlist is the TASK's defect, never the design's: an infrastructure
        error (RuntimeError) in `auto` as in `require`, before anything is weighed."""
        for mode in ("auto", "require"):
            with self.assertRaises(RuntimeError) as cm:
                checkpy.ppa_block(self.netlist(self.BROADCAST), {"depth": 1, "num_gates": 1}, mode,
                                  task={"name": "t", "input_drive": "sky130_fd_sc_hd__buf_3"})
            self.assertIn("task t: input_drive 'sky130_fd_sc_hd__buf_3' is not one of the allowed input drives",
                          str(cm.exception))

    @needs_lib
    def test_an_illegal_netlist_is_the_design_s_fault_in_every_mode(self):
        """A netlist the repair cannot make legal (IllegalNetlist; no real sky130 netlist of the pinned flow is known to be
        one, so the weighing is patched to say so) is the DESIGN's fault: the block says so with the net named, in `auto` as
        in `require` (it is not an infrastructure error), and the stage REJECTS the design at `ppa`."""
        sres = {"depth": 1, "num_gates": 1}
        net = self.netlist(self.BROADCAST)
        for mode in ("auto", "require"):
            with PATCHES["illegal"]():
                b = checkpy.ppa_block(net, sres, mode)
            self.assertEqual(set(b), {"available", "illegal", "reason", "legality"})
            self.assertEqual((b["available"], b["illegal"], b["legality"]["over_max_capacitance"]), (False, True, 1))
            self.assertIn("the net n (inv_1 g7), driving 99 cell pins", b["reason"])
            res, st = {}, {}
            with contextlib.redirect_stderr(io.StringIO()) as err:
                with self.assertRaises(checkpy.Reject) as cm, PATCHES["illegal"]():
                    checkpy.ppa_stage(res, st, net, sres, {}, mode)
            self.assertEqual(cm.exception.stage, "ppa")
            self.assertIn("so the design is rejected", cm.exception.msg)
            self.assertEqual(res["ppa"], b)
            self.assertEqual(st["ppa"]["mode"], mode)
            self.assertIn("ppa: REJECTED", err.getvalue())

    @needs_lib
    def test_a_repair_that_is_not_the_scored_circuit_is_infrastructure_in_require_only(self):
        sres = {"depth": 1, "num_gates": 1}
        with mock.patch.object(ppa, "analyze", side_effect=ppa.RepairDefect("differs at net y on vector 3")):
            b = checkpy.ppa_block(self.netlist(), sres, "auto")
            self.assertEqual(b, {"available": False,
                                 "reason": "the repaired netlist is not the scored circuit: differs at net y on vector 3"})
            with self.assertRaises(RuntimeError) as cm:
                checkpy.ppa_block(self.netlist(), sres, "require")
            self.assertIn("the repaired netlist is not the scored circuit", str(cm.exception))

    @needs_lib
    def test_disagreement_with_the_scorer_is_nothing_in_auto_and_an_error_in_require(self):
        sres = {"depth": 2, "num_gates": 1}
        b = checkpy.ppa_block(self.netlist(), sres, "auto")
        self.assertFalse(b["available"])
        self.assertIn("differs from score.py's", b["reason"])
        with self.assertRaises(RuntimeError) as cm:
            checkpy.ppa_block(self.netlist(), sres, "require")
        self.assertIn("differs from score.py's", str(cm.exception))


class InputDrivePrelude(Tmp):
    """sky130_a0_v3: check.py validates the task's `input_drive` in its infrastructure prelude (the task.json checks), so a
    task-configuration error costs no Lean stage, no synthesis and no simulation before it is reported. It needs the pins
    file only, not the liberty; a run that will not weigh (`--ppa off`, `--no-score`) does not look."""
    BAD = "sky130_fd_sc_hd__buf_3"
    MSG = f"task add: input_drive '{BAD}' is not one of the allowed input drives"

    def task_dir(self, **over):
        """A copy of tasks/add whose task.json has `over` (a fresh copy per call)."""
        tdir = os.path.join(self.tmp, "add")
        shutil.rmtree(tdir, ignore_errors=True)
        shutil.copytree(os.path.join(SVGOLF, "tasks", "add"), tdir)
        with open(os.path.join(tdir, "task.json")) as fh:
            task = json.load(fh)
        task.update(over)
        with open(os.path.join(tdir, "task.json"), "w") as fh:
            json.dump(task, fh)
        return tdir

    def check(self, tdir, mode, do_score=True, gate=None):
        """check() on add's reference, as `run_check` runs it; the source gate (the first stage after the prelude) and the
        Lean runner are replaced by tripwires."""
        orig = checkpy.Lean
        checkpy.Lean = FakeLean
        FakeLean.compiled = 0
        stage = tempfile.mkdtemp(prefix="svgolf-ppawiring-", dir=self.tmp)
        try:
            with contextlib.redirect_stderr(io.StringIO()), \
                    mock.patch.object(checkpy.envelope, "gate", side_effect=gate or AssertionError("the source gate ran")):
                return checkpy.check(tdir, os.path.join(tdir, "reference", "add_n.sv"), None, stage, [], do_score=do_score,
                                     build_trusted=False, unproved=True, postsynth_mode="light", ppa_mode=mode)
        finally:
            checkpy.Lean = orig

    def test_an_unknown_drive_stops_the_check_in_the_prelude(self):
        tdir = self.task_dir(input_drive=self.BAD)
        modes = ("auto", "require") if HAVE_LIB else ("auto",)
        for mode in modes:
            with self.subTest(mode=mode):
                with self.assertRaises(RuntimeError) as cm:
                    self.check(tdir, mode)
                self.assertIn(self.MSG, str(cm.exception))
                self.assertTrue(str(cm.exception).startswith("ppa: "), str(cm.exception))
                self.assertEqual(FakeLean.compiled, 0)
        # without the liberty too (`auto`): the allowlist is the pins file's
        with mock.patch.dict(os.environ, {"SVGOLF_SKY130_LIB": missing_lib()}):
            with self.assertRaises(RuntimeError) as cm:
                self.check(tdir, "auto")
            self.assertIn(self.MSG, str(cm.exception))
        for bad in (8, None, "buf_8", "SKY130_FD_SC_HD__BUF_8", "sky130_fd_sc_hd__buf_8 "):
            with self.subTest(bad=bad), self.assertRaises(RuntimeError) as cm:
                self.check(self.task_dir(input_drive=bad), "auto")
            self.assertIn("is not one of the allowed input drives", str(cm.exception))

    def test_a_run_that_does_not_weigh_does_not_look(self):
        """`--ppa off` and `--no-score` pass the prelude (the source gate, the next stage, is reached)."""
        tdir = self.task_dir(input_drive=self.BAD)

        class Reached(Exception):
            pass
        for kw in ({"mode": "off"}, {"mode": "auto", "do_score": False}):
            with self.subTest(**kw), self.assertRaises(Reached):
                self.check(tdir, gate=Reached("the source gate"), **kw)

    def test_an_allowed_drive_and_the_default_pass_the_prelude(self):
        class Reached(Exception):
            pass
        for over in ({}, {"input_drive": "sky130_fd_sc_hd__buf_1"}, {"input_drive": "sky130_fd_sc_hd__dfxtp_1"}):
            with self.subTest(**over), self.assertRaises(Reached):
                self.check(self.task_dir(**over), "auto", gate=Reached("the source gate"))

    def test_the_exit_status_is_2_with_the_json(self):
        tdir = self.task_dir(input_drive=self.BAD)
        # every lake/lean call prefixed by `false`: were the prelude to let the run through, no Lean would run anyway
        env = dict(os.environ, SVGOLF_LEAN_WRAP="false")
        proc = subprocess.run([PY, os.path.join(SVGOLF, "check.py"), tdir, os.path.join(tdir, "reference", "add_n.sv"),
                               "--unproved", "--sandbox", "off", "--no-trusted-build"], capture_output=True, text=True,
                              cwd=SVGOLF, timeout=120, env=env)
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
        out = json.loads(proc.stdout)
        self.assertEqual((out["accepted"], out["stage"]), (False, "infrastructure"))
        self.assertIn(self.MSG, out["errors"][0])
        self.assertNotIn("source", out.get("stages", {}))


@needs_flow
@needs_lib
class WithTheLiberty(unittest.TestCase):
    def test_the_weighed_netlist_is_the_one_postsynth_simulated(self):
        for task in TASKS:
            with self.subTest(task=task):
                res, _ = run_check(task, "auto")
                block = res["ppa"]
                self.assertTrue(block["available"])
                ps = res["stages"]["postsynth"]
                self.assertEqual(block["netlist_sha256"], ps["netlist_sha256"])     # no second synthesis
                again = ppa.weigh_netlist_file(os.path.join(res["postsynth_dir"], "netlist.v"))
                self.assertEqual({k: v for k, v in block.items() if k not in ("available", "mapped")}, again)   # A0' as ever
                sc = res["stages"]["score"]
                self.assertEqual(block["unit_depth"], sc["depth"])
                self.assertEqual(block["repair"]["cells_before"], sc["num_gates"])
                pins = ppa.Pins()
                self.assertEqual((block["ppa_version"], block["ppa_pins_sha256"], block["liberty_sha256"]),
                                 (pins.version, pins.sha256, pins.lib["sha256"]))
                self.assertEqual(block["ppa_script_sha256"], ppa.sha256_file(ppa.__file__))
                self.assertEqual(res["stages"]["ppa"]["mode"], "auto")

    def test_a_netlist_swapped_after_postsynth_is_not_weighed(self):
        """check(): the file is rewritten between the postsynth stage and the ppa stage (the netlist stays weighable, so
        only its hash gives it away): an infrastructure error, in `auto` as in `require`, never a `ppa` block."""
        for mode in ("auto", "require"):
            with self.subTest(mode=mode):
                with self.assertRaises(RuntimeError) as cm:
                    run_check("add", mode, tamper=True)
                self.assertIn("is not the one the postsynth stage verified", str(cm.exception))
        res, _ = run_check("add", "auto")                  # the control: the same run untampered
        self.assertEqual(res["ppa"]["netlist_sha256"], res["stages"]["postsynth"]["netlist_sha256"])

    def test_require_with_the_liberty_is_auto_with_its_mode_recorded(self):
        auto, _ = run_check("add", "auto")
        req, _ = run_check("add", "require")
        self.assertEqual(req["stages"]["ppa"]["mode"], "require")
        self.assertEqual(req["ppa"], auto["ppa"])
        self.assertEqual(req["stage"], "unproved")

    def test_golden_columns_of_the_references(self):
        """The `ppa` block of the check equals the golden of score/tests/ppa/expected_ppa.json."""
        with open(os.path.join(SVGOLF, "score", "tests", "ppa", "expected_ppa.json")) as fh:
            gold = json.load(fh)["designs"]
        for task, name in (("add", "add_ripple"), ("aes_sbox", "sbox_bp")):
            with self.subTest(task=task):
                res, _ = run_check(task, "auto")
                b, g = res["ppa"], gold[name]
                self.assertEqual((b["area_e4um2_sky130"], b["delay_ps_sky130"], b["unit_depth"], b["cells_sky130"],
                                  b["netlist_sha256"], b["repair"]["netlist_sha256"]),
                                 (g["area_e4um2"], g["delay_ps"], g["unit_depth"], g["cells"], g["netlist_sha256"],
                                  g["repaired_sha256"]))

    def test_an_illegal_design_is_rejected_at_the_ppa_stage(self):
        """check(): a design whose repaired sky130 netlist is illegal ends at stage `ppa`, not accepted, the audit's message
        the error; `ppa` says why; every stage before it ran as ever."""
        res, err = run_check("add", "require", patch="illegal")
        self.assertEqual((res["accepted"], res["stage"]), (False, "ppa"))
        self.assertIn("the net n (inv_1 g7), driving 99 cell pins", res["errors"][0])
        self.assertEqual((res["ppa"]["available"], res["ppa"]["illegal"]), (False, True))
        self.assertEqual(res["stages"]["ppa"]["mode"], "require")
        self.assertIn("postsynth", res["stages"])
        self.assertIn("ppa: REJECTED", err)


@needs_flow
@needs_lib
class DeadWireNetlists(unittest.TestCase):
    """The review's major finding, through check.py's own stages (source, extract, banlist, fourstate, score, postsynth, ppa;
    a fake Lean for the `design` stage): admissible `aes_sbox` designs whose scored netlist carries the dead public-named
    wires Yosys leaves of techmapped cells (a run-time shift, a one-hot decode, a run-time bit select) end at the
    pseudo-stage `unproved` WITH their columns, in `require` as in `auto`. The reader once answered `assign width mismatch` for every one
    of them, so a leaderboard record of such a design silently had no columns."""
    DESIGNS = {"sbox_shift": (3828672, 1101, 5), "sbox_onehot": (1188640, 705, 3), "sbox_bitsel": (713184, 910, 4)}   # sky130_a0_v3

    def test_the_columns_of_designs_with_dead_wires(self):
        for name, (area_e4, delay_ps, depth) in self.DESIGNS.items():
            with self.subTest(design=name):
                path = os.path.join(HERE, "ppa_wiring", "dead_wire_designs", name + ".sv")
                for mode in ("require", "auto") if name == "sbox_shift" else ("require",):
                    res, err = run_check("aes_sbox", mode, design=path)
                    self.assertEqual(res["stage"], "unproved", res["errors"])
                    b = res["ppa"]
                    self.assertTrue(b["available"], b)
                    self.assertEqual((b["area_e4um2_sky130"], b["delay_ps_sky130"], b["unit_depth"]),
                                     (area_e4, delay_ps, depth))
                    self.assertEqual(b["unit_depth"], res["score"]["depth"])
                    self.assertEqual(b["netlist_sha256"], res["stages"]["postsynth"]["netlist_sha256"])
                    self.assertIn("ppa: ", err)
                    self.assertNotIn("not computed", err)
                # the netlist the stage weighed really has the escaped wires the test is about
                with open(os.path.join(run_check("aes_sbox", "require", design=path)[0]["postsynth_dir"], "netlist.v")) as fh:
                    self.assertRegex(fh.read(), r"(?m)^\s*wire\b[^;\n]*\\\S+ ;")


@needs_flow
@needs_lib
class MappedFlow(unittest.TestCase):
    """WP-X4: flow A1' through check.py's own stages. The `ppa` block of a weighed design carries `mapped`, the real
    `abc -liberty` mapping of the canonical RTLIL of the same score run; everything else of the result is what it was."""

    @classmethod
    def gold(cls):
        with open(os.path.join(SVGOLF, "score", "tests", "ppa", "expected_ppa_mapped.json")) as fh:
            return json.load(fh)["designs"]

    def test_the_references_carry_the_golden_mapped_columns(self):
        for task, name in (("add", "add_ripple"), ("aes_sbox", "sbox_bp")):
            for mode in ("auto", "require"):
                with self.subTest(task=task, mode=mode):
                    res, err = run_check(task, mode)
                    m, g = res["ppa"]["mapped"], self.gold()[name]
                    self.assertTrue(m["available"], m)
                    self.assertEqual((m["area_e4um2_sky130_mapped_v1"], m["mapped_delay_sky130_v1"], m["mapped_cells_sky130_v1"],
                                      m["mapped_levels_sky130_v1"], m["netlist_sha256"], m["rtlil_sha256"]),
                                     (g["area_e4um2"], g["delay_ps"], g["cells"], g["levels"], g["netlist_sha256"],
                                      g["rtlil_sha256"]))
                    self.assertEqual(m["rtlil_sha256"], res["stages"]["score"]["rtlil_sha256"])    # the same circuit as the score
                    self.assertNotEqual(m["netlist_sha256"], res["stages"]["postsynth"]["netlist_sha256"])   # another netlist
                    self.assertIn("ppa: mapped (A1'", err)
                    self.assertEqual(res["stage"], "unproved")

    def test_the_rest_of_ppa_is_what_it_was(self):
        """`ppa` minus `mapped` is exactly A0''s block (the weighed netlist file's), the result minus `ppa` is the
        baseline's, and the stage record gains one key."""
        for task in TASKS:
            with self.subTest(task=task):
                res, _ = run_check(task, "auto")
                block = res["ppa"]
                again = ppa.weigh_netlist_file(os.path.join(res["postsynth_dir"], "netlist.v"))
                self.assertEqual({k: v for k, v in block.items() if k not in ("available", "mapped")}, again)
                self.assertEqual(set(block) - set(again), {"available", "mapped"})
                self.assertEqual(set(res["stages"]["ppa"]), {"mode", "seconds", "mapped_seconds"})
                self.assertGreaterEqual(res["stages"]["ppa"]["seconds"], res["stages"]["ppa"]["mapped_seconds"])
                self.assertEqual(bi.render(bi.without_ppa(bare(res))), bi.golden(task, "unproved"))

    def test_the_mapped_block_is_the_function_of_the_two_files(self):
        """`ppa_mapped_block` on the files of a real run gives the block the stage recorded (a pure function of the files)."""
        res, _ = run_check("add", "auto")
        tdir = res["postsynth_dir"]
        again = checkpy.ppa_mapped_block(os.path.join(tdir, "canon.il"), "add_n", os.path.join(tdir, "netlist.v"), "require",
                                         expect_rtlil_sha256=res["stages"]["score"]["rtlil_sha256"],
                                         expect_netlist_sha256=res["stages"]["postsynth"]["netlist_sha256"])
        self.assertEqual(again, res["ppa"]["mapped"])

    def test_a_mapping_the_flow_cannot_do_is_a_reason_and_the_check_goes_on(self):
        for mode in ("auto", "require"):
            with self.subTest(mode=mode):
                res, err = run_check("add", mode, patch="mapfail")
                self.assertEqual(res["stage"], "unproved", res["errors"])
                self.assertTrue(res["ppa"]["available"])                     # A0' is untouched
                self.assertEqual(res["ppa"]["mapped"], {"available": False, "reason": "the mapping run failed: boom detail"})
                self.assertIn("ppa: mapped columns not computed: the mapping run failed: boom detail", err)
                ok, _ = run_check("add", mode)
                self.assertEqual({k: v for k, v in res["ppa"].items() if k != "mapped"},
                                 {k: v for k, v in ok["ppa"].items() if k != "mapped"})

    def test_a_mapped_netlist_that_is_not_the_scored_circuit_and_a_defect_are_infrastructure_errors_in_require_only(self):
        for patch, why in (("defect", "the mapped netlist is not the scored circuit: differs at y[0] on vector 3"),
                           ("boom", "ppa.py failed on this design's mapping: ValueError: boom")):
            with self.subTest(patch=patch):
                res, _ = run_check("add", "auto", patch=patch)
                self.assertEqual(res["stage"], "unproved")
                self.assertEqual(res["ppa"]["mapped"], {"available": False, "reason": why})
                with self.assertRaises(RuntimeError) as cm:
                    run_check("add", "require", patch=patch)
                self.assertIn("ppa: " + why, str(cm.exception))

    def test_a_canonical_rtlil_changed_after_the_score_stage_is_not_mapped(self):
        """Like a swapped netlist: the file the mapping would read is not the bytes the score stage hashed. An infrastructure
        error in every mode, never a block."""
        for mode in ("auto", "require"):
            with self.subTest(mode=mode):
                with self.assertRaises(RuntimeError) as cm:
                    run_check("add", mode, tamper="rtlil")
                self.assertIn("canonical RTLIL the mapping reads", str(cm.exception))
                self.assertIn("changed in between", str(cm.exception))

    def test_off_never_maps_and_asks_the_score_stage_for_no_rtlil(self):
        with mock.patch.object(ppa, "map_rtlil", side_effect=AssertionError("off mapped")):
            res, err = checkpy_run_off()
        self.assertNotIn("ppa", res)
        self.assertNotIn("mapped", err)

    def test_a_design_with_constants_has_one_tie_cell_in_both_flows(self):
        with tempfile.TemporaryDirectory() as d:
            sv = os.path.join(d, "cst.sv")
            with open(sv, "w") as fh:
                fh.write("module aes_sbox(input logic [7:0] x, output logic [7:0] y);\n"
                         "  assign y = {4'b1010, x[3:0] ^ x[7:4]};\nendmodule\n")
            res, _ = run_check("aes_sbox", "require", design=sv)
        b = res["ppa"]
        self.assertTrue(b["constants"] and b["mapped"]["constants"], b)
        self.assertEqual(b["cell_hist_sky130"]["conb_1"], 1)
        self.assertEqual(b["mapped"]["mapped_cell_hist_sky130_v1"]["conb_1"], 1)


class MappedBlock(Tmp):
    """`ppa_mapped_block`, the function behind the stage, on synthetic files (no flow needed)."""

    def files(self):
        il = os.path.join(self.tmp, "canon.il")
        net = os.path.join(self.tmp, "netlist.v")
        with open(il, "w") as fh:
            fh.write("# an RTLIL\n")
        with open(net, "w") as fh:
            fh.write(PpaBlock.TINY)
        return il, net

    def test_an_absent_liberty_is_a_reason_in_auto_and_an_infrastructure_error_in_require(self):
        il, net = self.files()
        with mock.patch.dict(os.environ, {"SVGOLF_SKY130_LIB": missing_lib()}):
            b = checkpy.ppa_mapped_block(il, "tiny", net, "auto")
            self.assertEqual(set(b), {"available", "reason"})
            self.assertIn("liberty not found", b["reason"])
            with self.assertRaises(RuntimeError) as cm:
                checkpy.ppa_mapped_block(il, "tiny", net, "require")
            self.assertIn("ppa: liberty not found", str(cm.exception))

    def test_files_that_are_not_the_recorded_bytes_are_an_integrity_failure_in_every_mode(self):
        il, net = self.files()
        with open(il, "rb") as fh:
            il_sha = ppa.sha256_bytes(fh.read())
        with open(net, "rb") as fh:
            net_sha = ppa.sha256_bytes(fh.read())
        with mock.patch.object(ppa, "open_library", return_value=(mock.Mock(), ppa.Pins())):
            for mode in ("auto", "require"):
                with self.assertRaises(RuntimeError, msg=mode) as cm:
                    checkpy.ppa_mapped_block(il, "tiny", net, mode, expect_rtlil_sha256="0" * 64)
                self.assertIn("canonical RTLIL the mapping reads", str(cm.exception))
                with self.assertRaises(RuntimeError, msg=mode) as cm:
                    checkpy.ppa_mapped_block(il, "tiny", net, mode, expect_rtlil_sha256=il_sha, expect_netlist_sha256="1" * 64)
                self.assertIn("netlist file the mapping reads", str(cm.exception))
                with mock.patch.object(ppa, "mapped_block", return_value={"available": False, "reason": "x"}):
                    self.assertEqual(checkpy.ppa_mapped_block(il, "tiny", net, mode, expect_rtlil_sha256=il_sha,
                                                              expect_netlist_sha256=net_sha),
                                     {"available": False, "reason": "x"})

    def test_a_stage_without_an_rtlil_has_no_mapped_key(self):
        """`ppa_stage` called the way WP-X3 called it (no RTLIL): the block is A0''s alone, as before."""
        _, net = self.files()
        res, st = {}, {"postsynth": {}}
        sres = {"depth": 1, "num_gates": 1}
        with mock.patch.object(checkpy, "ppa_block", return_value={"available": True, "area_um2_sky130": 1,
                                                                   "delay_ps_sky130": 2, "unit_depth": 1,
                                                                   "ppa_version": "v"}):
            checkpy.ppa_stage(res, st, net, sres, {}, "auto")
        self.assertNotIn("mapped", res["ppa"])
        self.assertEqual(set(st["ppa"]), {"mode", "seconds"})


class LibertyRequired(unittest.TestCase):
    def test_liberty_present_when_required(self):
        if REQUIRE_LIB and not HAVE_LIB:
            self.fail(f"SVGOLF_PPA_REQUIRE_LIB=1 but the pinned liberty is absent: {REAL_LIB}")


class Tripwire(Tmp):
    """The integrity tripwire (check.py, `integrity_snapshot`) fingerprints score/ppa.py and score/ppa_pins.json BY
    CONTENT: an edit of either, between two snapshots, is a difference. Run on a copy of the two files (the real ones are
    the checker's)."""

    def snapshot(self, root):
        stage = os.path.join(self.tmp, "stage")
        os.makedirs(stage, exist_ok=True)
        with mock.patch.object(checkpy, "SVGOLF", root), mock.patch.object(checkpy, "LS_ROOT", self.tmp), \
                mock.patch.object(checkpy, "_tool_trees", return_value=[]), \
                mock.patch.object(postsynth, "trusted_files", side_effect=postsynth.InfraError("none here")):
            return checkpy.integrity_snapshot(stage)

    def make_tree(self):
        root = os.path.join(self.tmp, "svgolf")
        os.makedirs(os.path.join(root, "score"))
        for f in ("ppa.py", "ppa_pins.json", "ppa_mapped.ys", "ppa_mapped_pins.json", "score.py"):
            shutil.copyfile(os.path.join(SVGOLF, "score", f), os.path.join(root, "score", f))
        return root

    def test_both_files_are_fingerprinted_by_content(self):
        root = self.make_tree()
        snap = self.snapshot(root)
        for f in ("ppa.py", "ppa_pins.json", "ppa_mapped.ys", "ppa_mapped_pins.json"):
            p = os.path.join(root, "score", f)
            self.assertIn(p, snap, f)
            self.assertEqual(snap[p], "sha256:" + checkpy.sha256_file(p))

    def test_an_edit_of_either_file_is_caught_and_nothing_else_is(self):
        root = self.make_tree()
        before = self.snapshot(root)
        self.assertEqual(checkpy.integrity_diff(before, self.snapshot(root)), [])
        for f, edit in (("ppa.py", b"\n# a solution's build edited this\n"), ("ppa_pins.json", b" "),
                        ("ppa_mapped.ys", b"\n# edited\n"), ("ppa_mapped_pins.json", b" ")):
            p = os.path.join(root, "score", f)
            with open(p, "rb") as fh:
                orig = fh.read()
            with open(p, "ab") as fh:
                fh.write(edit)
            self.assertEqual(checkpy.integrity_diff(before, self.snapshot(root)), [p], f)
            with open(p, "wb") as fh:
                fh.write(orig)
        self.assertEqual(checkpy.integrity_diff(before, self.snapshot(root)), [])

    def test_the_real_check_names_both_files(self):
        """The list in check.py itself (the copy above exercises the same code path)."""
        with open(os.path.join(SVGOLF, "check.py")) as fh:
            src = fh.read()
        self.assertIn('"svgolf.ys", "ge.json", "ppa.py", "ppa_pins.json", "ppa_mapped.ys",\n                 "ppa_mapped_pins.json")', src)


class Help(unittest.TestCase):
    def test_flag_is_documented(self):
        proc = subprocess.run([PY, os.path.join(SVGOLF, "check.py"), "--help"], capture_output=True, text=True)
        self.assertIn("--ppa {auto,off,require}", proc.stdout)
        self.assertIn("default board", " ".join(proc.stdout.split()))


if __name__ == "__main__":
    unittest.main(verbosity=1)
