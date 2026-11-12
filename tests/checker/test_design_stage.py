#!/usr/bin/env python3.12
"""The `design` stage's rejection of an Unsupported construct (WP-C3), without Lean:
`check.py`'s real source/extract/banlist/fourstate stages run on a reference design
(pyslang, the extractor and Yosys, no Lean, no Verilator), and the Lean runner is a
fake whose `compile` of the generated `Submission.Design` answers what Lean would:

  * the generated module is written, with the `#eval` that tests
    `Design2.hasUnsupported` at every probe point and names `firstLoud`;
  * a Lean error carrying `SVGOLF_UNSUPPORTED at <point>: <kind>: <text>` is a REJECTION
    at `design` whose message names the first unsupported construct and the point;
  * any other Lean error keeps the old message ("the design does not load");
  * a compile with NO `SVGOLF_UNSUPPORTED_FREE <n>` marker is an infrastructure error
    (a check that did not run is not a pass);
  * the marker is recorded as `stages.design.unsupported_free_points`;

and the `solution` stage with a fake compile of `Solution.lean` (item 9 of the from-scratch study): a
timeout names the last declaration that finished, the progress lines are not kept as messages, and a
proof that saw the progress trace is compiled again without it; and the `comparator` and `leanchecker`
stages with fake runs (`VerifyStages`): both get the task's CPU limit and its wall-clock backstop,
record both readings, and a timeout says which limit stopped it.

The real Lean side is exercised by `tests/run.py` (the attacks `func_call`,
`assign_func`, `fn_uninit`, `latch_never` and `latch_star` of `tests/_example/attacks/`,
rejected at `design`, and every reference accepted).

    python3.12 tests/checker/test_design_stage.py
"""

import importlib.util
import json
import os
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


checkpy = load("svgolf_check_py_design", os.path.join(SVGOLF, "check.py"))
TASK = os.path.join(SVGOLF, "tasks", "_example")
SV = os.path.join(TASK, "reference", "band.sv")


class FakeLean:
    """Stands in for check.py's `Lean`: `compile` answers `answer` = (rc, output, seconds)."""
    answer = (0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.5)
    compiled = []

    def __init__(self, stage, wrap):
        self.stage, self.wrap = stage, wrap

    def run(self, args, timeout=None, lake_env=True, **kw):
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        with open(module_path) as fh:
            FakeLean.compiled.append(fh.read())
        return FakeLean.answer


class DesignStage(unittest.TestCase):
    def run_check(self, answer):
        FakeLean.answer, FakeLean.compiled = answer, []
        stage = tempfile.mkdtemp(prefix="svgolf-designtest-")
        self.addCleanup(shutil.rmtree, stage, ignore_errors=True)
        orig = checkpy.Lean
        checkpy.Lean = FakeLean
        try:
            return checkpy.check(TASK, SV, None, stage, [], do_score=False, build_trusted=False,
                                 unproved=True)
        finally:
            checkpy.Lean = orig

    def test_loud_design_is_rejected_at_design_naming_the_construct(self):
        msg = ("Submission/Design.lean:20:0: error: SVGOLF_UNSUPPORTED at N=16: "
               "Call:both: both(a, b)\n")
        res = self.run_check((1, msg, 2.0))
        self.assertEqual((res["accepted"], res["stage"]), (False, "design"))
        (err,) = res["errors"]
        self.assertIn("ls-sv cannot run it", err)
        self.assertIn("unsupported construct", err)
        self.assertIn("N=16: Call:both: both(a, b)", err)
        self.assertIn("Rewrite the design without the construct", err)
        self.assertNotIn("does not load", err)

    def test_the_generated_module_carries_the_check(self):
        self.run_check((0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.0))
        (text,) = FakeLean.compiled
        self.assertIn("load_design_sv2 design from", text)
        self.assertIn("d.hasUnsupported", text)
        self.assertIn("d.firstLoud", text)
        for pt in ("N=1", "N=2", "N=3", "N=16"):         # _example's probe points (all <= 16)
            self.assertIn(f'("{pt}", design.sem', text)

    def test_an_ordinary_load_failure_keeps_its_message(self):
        res = self.run_check((1, "Submission/Design.lean:3:0: error: load_design_sv2: REFUSED\n",
                              1.0))
        self.assertEqual(res["stage"], "design")
        self.assertIn("the design does not load (ls-sv refused it)", res["errors"][0])

    def test_a_check_that_printed_nothing_is_not_a_pass(self):
        with self.assertRaises(RuntimeError) as cm:
            self.run_check((0, "", 1.0))
        self.assertIn("unsupported-construct check printed nothing", str(cm.exception))

    def test_a_clean_design_records_the_points_checked(self):
        res = self.run_check((0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.5))
        self.assertEqual(res["stage"], "unproved")
        self.assertEqual(res["stages"]["design"],
                         {"exit": 0, "seconds": 1.5, "unsupported_free_points": 4})
        # a CLEAN --unproved run (the 11/05 newcomer study): not accepted, nothing under `errors`, its sentence a
        # note, `unproved_ok` (check.py's main exits 0 on it)
        self.assertEqual((res["accepted"], res["errors"], res["unproved_ok"]), (False, [], True))
        (note,) = res["notes"]
        self.assertTrue(note.startswith("--unproved: every check that needs no proof passed"), note)

    def test_a_missing_tool_is_an_infrastructure_error_that_says_what_to_do(self):
        """B5 of the 11/05 newcomer study: no traceback, a remedy. Yosys missing (it used to be a FileNotFoundError
        traceback in the banlist backstop, exit 1), and the extractor missing (the fresh-clone error, which now says
        to run `lake build`)."""
        from unittest import mock
        with mock.patch.dict(os.environ, {"SVGOLF_YOSYS": "/nonexistent/yosys"}):
            with self.assertRaises(RuntimeError) as cm:
                self.run_check((0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.0))
        self.assertIn("Yosys is not on PATH (infrastructure", str(cm.exception))
        with mock.patch.object(checkpy.envelope, "EXTRACTOR", "/nonexistent/extract.py"):
            with self.assertRaises(RuntimeError) as cm:
                self.run_check((0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.0))
        self.assertIn("run `lake build` from the repository root first (README, Building)", str(cm.exception))

    def test_the_first_lean_error_survives_a_long_refusal(self):
        """B2: a long Lean output keeps its first error line in `errors` (a tail kept only the end)."""
        long = ("/s/Submission/Design.lean:7:0: error: the FIRST refusal\n" + "goal dump line\n" * 600
                + "/s/Submission/Design.lean:9:0: error: a later one\n")
        res = self.run_check((1, long, 1.0))
        self.assertEqual(res["stage"], "design")
        self.assertIn("Design.lean:7:0: error: the FIRST refusal", res["errors"][0])
        self.assertIn("Design.lean:9:0: error: a later one", res["errors"][0])
        self.assertNotIn("unproved_ok", res)


class FakeSolutionLean(FakeLean):
    """`FakeLean` whose compile of `Solution.lean` answers the next of `answers` = (rc, output, seconds, progress), sets
    `progress` as the real runner does, and records the keyword arguments of each such compile."""
    answers, kws = [], []

    def run(self, args, timeout=None, lake_env=True, **kw):
        if args[:2] == ["printenv", "LEAN_PATH"]:          # one search-path entry, which the tripwire may hash
            return 0, os.path.join(self.stage, "build") + "\n", 0.1
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        if os.path.basename(module_path) != "Solution.lean":
            return 0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.0
        FakeSolutionLean.kws.append(dict(kw, timeout=timeout))
        rc, out, el, self.progress, *usage = FakeSolutionLean.answers.pop(0)
        self.usage = usage[0] if usage else None
        return rc, out, el


class SolutionStage(unittest.TestCase):
    """The `solution` stage (item 9 of the from-scratch study): the compile asks for progress; a timeout names the last
    declaration that finished; the progress lines never reach `messages`; a proof that saw the trace is compiled again
    without it, and that verdict stands. The real Lean side is `tests/run.py`'s attack `slow_proof`."""
    LINE = "[Kernel] \u2705\ufe0f typechecking declarations [{}]\n"
    PROGRESS = {"finished": 12, "auxiliary": 0, "run_s": 20.0,
                "last": {"decls": "Submission.band_interface", "at_s": 1.9},
                "slowest": [{"decls": "Submission.band_comb", "s": 0.4}]}

    def run_check(self, answers):
        FakeSolutionLean.answers, FakeSolutionLean.kws = list(answers), []
        stage = tempfile.mkdtemp(prefix="svgolf-solutiontest-")
        self.addCleanup(shutil.rmtree, stage, ignore_errors=True)
        orig = checkpy.Lean
        checkpy.Lean = FakeSolutionLean
        try:
            return checkpy.check(TASK, SV, os.path.join(TASK, "reference", "band.lean"), stage, [], time_limit=20,
                                 do_score=False, build_trusted=False)
        finally:
            checkpy.Lean = orig

    def test_a_timeout_names_the_last_declaration_that_finished(self):
        """Stopped at the CPU limit (decided 2026-11-05: the limit counts CPU seconds): the rejection gives the CPU and
        the wall seconds apart, then where the time went."""
        res = self.run_check([(124, self.LINE.format("Submission.band_interface")
                               + "SVGOLF_TIMEOUT after 20.00s cpu_s=20.30 by=cpu\n", 20.0, self.PROGRESS,
                               {"wall_s": 20.0, "cpu_s": 20.3, "stopped_by": "cpu"})])
        self.assertEqual((res["accepted"], res["stage"]), (False, "solution"))
        (err,) = res["errors"]
        self.assertTrue(err.startswith("the proof did not compile within the 20 s CPU limit: Lean used 20.3 CPU s in "
                                       "20.0 s of wall clock and was stopped; where the time went: 12 declarations "
                                       "finished"), err)
        self.assertIn("the last `Submission.band_interface` 1.9 s into the run; the 18.1 s after it", err)
        sol = res["stages"]["solution"]
        self.assertEqual(sol["progress"], self.PROGRESS)
        self.assertEqual((sol["cpu_seconds"], sol["seconds"], sol["stopped_by"], sol["time_limit_s"],
                          sol["time_limit_counts"], sol["wall_limit_s"]), (20.3, 20.0, "cpu", 20, "cpu", 100))
        self.assertNotIn("[Kernel]", sol["messages"])
        (kw,) = FakeSolutionLean.kws
        # the CPU limit is the task's (here --time-limit 20), the wall clock its backstop, SOLUTION_WALL_FACTOR x it
        self.assertEqual((kw["progress"], kw["timeout"], kw["cpu_limit"]), (True, 100, 20))

    def test_a_proof_that_waits_meets_the_wall_clock_backstop(self):
        res = self.run_check([(124, "SVGOLF_TIMEOUT after 100.05s cpu_s=2.10 by=wall\n", 100.0, None,
                               {"wall_s": 100.0, "cpu_s": 2.1, "stopped_by": "wall"})])
        (err,) = res["errors"]
        self.assertEqual(err, "the proof did not compile within the 100 s wall-clock backstop: Lean used 2.1 CPU s of "
                              "its 20 s CPU limit in 100.0 s and was stopped, so it waited (a `sleep`, blocked I/O, a "
                              "machine too loaded to run it)")
        self.assertEqual(res["stages"]["solution"]["stopped_by"], "wall")

    def test_a_proof_that_saw_the_trace_is_compiled_again_without_it(self):
        seen = ("Solution.lean:9:0: error: \u274c\ufe0f Docstring on `#guard_msgs` does not match generated message:\n\n"
                "trace: " + self.LINE.format("Submission.h"))
        res = self.run_check([(1, seen, 2.0, self.PROGRESS),
                              (1, "Solution.lean:3:0: error: the real one\n", 2.1, None)])
        self.assertEqual([k.get("progress", False) for k in FakeSolutionLean.kws], [True, False])
        self.assertEqual(res["stage"], "solution")
        self.assertIn("the real one", res["errors"][0])
        self.assertNotIn("guard_msgs", res["errors"][0])
        sol = res["stages"]["solution"]
        self.assertTrue(sol["progress_retried"])
        self.assertNotIn("progress", sol)
        self.assertEqual(sol["seconds"], 2.1)

    def test_an_ordinary_failure_is_compiled_once(self):
        res = self.run_check([(1, "Solution.lean:3:0: error: unsolved goals\n" + self.LINE.format("Submission.a"),
                               2.0, self.PROGRESS)])
        self.assertEqual(len(FakeSolutionLean.kws), 1)
        self.assertNotIn("[Kernel]", res["errors"][0])
        self.assertNotIn("progress_retried", res["stages"]["solution"])


def solution_imports(path):
    """The imports a compiled `Solution.lean` records (its header's, and `Init`), as the comparator reports them."""
    with open(path) as fh:
        return ["Init"] + [ln.split()[1] for ln in fh if ln.startswith("import ")]


class FakeVerifyLean(FakeSolutionLean):
    """`FakeSolutionLean` whose compile of `Solution.lean` succeeds and whose comparator (`lean --run`) and `leanchecker`
    runs answer `answers[kind]` = (rc, output, seconds, usage), setting `usage` as the real runner does, and record the
    keyword arguments of each such run (`kws[kind]`)."""
    answers, kws = {}, {}

    def run(self, args, timeout=None, lake_env=True, **kw):
        kind = "comparator" if args[:2] == ["lean", "--run"] else "leanchecker" if args[:1] == ["leanchecker"] else None
        if kind is None:
            return super().run(args, timeout, lake_env, **kw)
        FakeVerifyLean.kws[kind] = dict(kw, timeout=timeout)
        rc, out, el, self.usage = FakeVerifyLean.answers[kind]
        return rc, out, el

    def compile(self, module_path, timeout=None, **kw):
        if os.path.basename(module_path) != "Solution.lean":
            return 0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.0
        self.progress, self.usage = None, {"wall_s": 2.0, "cpu_s": 3.0, "stopped_by": None}
        return 0, "", 2.0


class VerifyStages(unittest.TestCase):
    """The comparator and `leanchecker` (the replay of the compiled modules) count CPU seconds against the task's
    `verify_time_limit_s`, with a wall-clock backstop of VERIFY_WALL_FACTOR times it (since 2026-11-06; before, the limit
    was wall clock, so the machine's load could reject an honest record). The fixtures with the real supervisor, a
    replay that computes and one that sleeps, are tests/checker/test_advisories.py's `FakeWrapperLean`."""
    LEAN = os.path.join(TASK, "reference", "band.lean")
    OK = {"accepted": True, "axioms": ["propext"], "errors": [], "goal": "Submission.Goal"}

    def run_check(self, comparator, leanchecker=None):
        comp_ok = (0, "SVGOLF_COMPARATOR " + json.dumps(dict(self.OK, imports={
            "Submission.Solution": solution_imports(self.LEAN)})) + "\n", 12.0,
                   {"wall_s": 12.0, "cpu_s": 14.5, "stopped_by": None})
        FakeVerifyLean.answers = {"comparator": comp_ok if comparator == "ok" else comparator,
                                  "leanchecker": leanchecker or (0, "", 11.0, {"wall_s": 11.0, "cpu_s": 10.2,
                                                                                "stopped_by": None})}
        FakeVerifyLean.kws = {}
        stage = tempfile.mkdtemp(prefix="svgolf-verifytest-")
        self.addCleanup(shutil.rmtree, stage, ignore_errors=True)
        orig = checkpy.Lean
        checkpy.Lean = FakeVerifyLean
        try:
            return checkpy.check(TASK, SV, self.LEAN, stage, [], do_score=False, build_trusted=False)
        finally:
            checkpy.Lean = orig

    def limits(self):
        with open(os.path.join(TASK, "task.json")) as fh:
            v = json.load(fh).get("verify_time_limit_s", checkpy.VERIFY_TIME_LIMIT_S)
        return v, checkpy.VERIFY_WALL_FACTOR * v

    def test_both_runs_get_the_cpu_limit_and_the_backstop_and_record_both_readings(self):
        res = self.run_check("ok")
        self.assertTrue(res["accepted"], res["errors"])
        cpu, wall = self.limits()
        self.assertEqual((cpu, wall), (900, 4500))
        for kind, (sec, c) in (("comparator", (12.0, 14.5)), ("leanchecker", (11.0, 10.2))):
            self.assertEqual((FakeVerifyLean.kws[kind]["timeout"], FakeVerifyLean.kws[kind]["cpu_limit"]), (wall, cpu))
            rec = res["stages"][kind]
            self.assertEqual((rec["exit"], rec["seconds"], rec["cpu_seconds"], rec["time_limit_s"],
                              rec["time_limit_counts"], rec["wall_limit_s"]), (0, sec, c, cpu, "cpu", wall))
            self.assertNotIn("stopped_by", rec)
        self.assertTrue(res["stages"]["comparator"]["result"]["accepted"])

    def test_a_comparator_that_computes_past_its_cpu_limit(self):
        res = self.run_check((124, "SVGOLF_TIMEOUT after 310.20s cpu_s=900.40 by=cpu\n", 310.2,
                              {"wall_s": 310.2, "cpu_s": 900.4, "stopped_by": "cpu"}))
        self.assertEqual((res["accepted"], res["stage"]), (False, "comparator"))
        self.assertEqual(res["errors"], ["the comparator did not finish within the 900 s CPU limit: the comparator used "
                                         "900.4 CPU s in 310.2 s of wall clock and was stopped"])
        rec = res["stages"]["comparator"]
        self.assertEqual((rec["exit"], rec["stopped_by"], rec["cpu_seconds"], rec["result"]), (124, "cpu", 900.4, None))
        self.assertNotIn("leanchecker", res["stages"])

    def test_a_replay_that_waits_meets_the_wall_clock_backstop(self):
        res = self.run_check("ok", (124, "SVGOLF_TIMEOUT after 4500.05s cpu_s=3.20 by=wall\n", 4500.0,
                                    {"wall_s": 4500.0, "cpu_s": 3.2, "stopped_by": "wall"}))
        self.assertEqual((res["accepted"], res["stage"]), (False, "leanchecker"))
        self.assertEqual(res["errors"], ["kernel replay did not finish within the 4500 s wall-clock backstop: leanchecker "
                                         "used 3.2 CPU s of its 900 s CPU limit in 4500.0 s and was stopped, so it "
                                         "waited (a `sleep`, blocked I/O, a machine too loaded to run it)"])
        self.assertEqual(res["stages"]["leanchecker"]["stopped_by"], "wall")

    def test_a_loaded_machine_does_not_reject_an_honest_replay(self):
        """The case the wall-clock limit got wrong: 1200 s of wall clock (over the former 900 s limit) for 40 CPU s."""
        res = self.run_check("ok", (0, "", 1200.0, {"wall_s": 1200.0, "cpu_s": 40.0, "stopped_by": None}))
        self.assertTrue(res["accepted"], res["errors"])
        self.assertEqual((res["stages"]["leanchecker"]["seconds"], res["stages"]["leanchecker"]["cpu_seconds"]),
                         (1200.0, 40.0))


class Completeness(unittest.TestCase):
    """An ACCEPTED result says whether the check was complete (`incomplete_reasons`; the universal-correctness audit,
    F10): `--no-score`, a LIGHT post-synthesis check (combinational or at any clocked point), `--no-trusted-build` and
    a `--time-limit` other than the task's make it incomplete, so that no board ranks it."""
    TASK = {"time_limit_s": 300}

    def reasons(self, st=None, do_score=True, build_trusted=True, time_limit=None):
        return checkpy.incomplete_reasons(self.TASK, st if st is not None else {"postsynth": {"mode": "full"}},
                                          do_score, build_trusted, time_limit)

    def test_a_complete_check(self):
        self.assertEqual(self.reasons(), [])
        self.assertEqual(self.reasons(time_limit=300), [])               # the task's own limit, given explicitly
        self.assertEqual(self.reasons({"postsynth": {"points": [{"mode": "full"}, {"mode": "full"}]}}), [])

    def test_each_omission_is_named(self):
        self.assertIn("--no-score", self.reasons(do_score=False)[0])
        self.assertIn("LIGHT", self.reasons({"postsynth": {"mode": "light"}})[0])
        self.assertIn("LIGHT", self.reasons({"postsynth": {"points": [{"mode": "full"}, {"mode": "light"}]}})[0])
        self.assertIn("--no-trusted-build", self.reasons(build_trusted=False)[0])
        self.assertIn("--time-limit 20", self.reasons(time_limit=20)[0])
        self.assertEqual(len(self.reasons({"postsynth": {"mode": "light"}}, build_trusted=False, time_limit=20)), 3)

    def test_the_light_reason_asks_for_no_second_run(self):
        """A plain run's check is light, and `leaderboard.py add` runs the full one itself: the reason says so, and
        starts with the words `leaderboard.py` tests to let a light record through (`acceptance_problems`)."""
        why = self.reasons({"postsynth": {"mode": "light"}})[0]
        self.assertTrue(why.startswith("the post-synthesis check ran LIGHT"), why)
        self.assertIn("leaderboard.py add runs the full check itself, so there is no need to rerun with --postsynth "
                      "full first", why)


if __name__ == "__main__":
    unittest.main(verbosity=1)
