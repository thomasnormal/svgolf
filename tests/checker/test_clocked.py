#!/usr/bin/env python3.12
"""The clocked checker's front end (PLAN4 Gate 2, steps 1 and 2), without Lean:

  * the source gate's clocked rules (score/srcgate.py item 6): every refusal fixture of
    `tests/seq_counter/attacks/` (one rule each, its first line `// expect: <message>`) is refused
    with exactly that one finding under the task's clock, and passes the combinational gate; the
    counter (`tests/seq_counter/reference/cnt.sv`) and the matmul reference pass the clocked gate;
  * the kinds (`task_kind`), the latency header (`parse_latency`) and the generated goal
    (`goal_text`: `Statement design.sem lat ∧ lat p₀ = n` for tx-family and stream-family);
  * check.py itself on the counter task, a tx-family task built on the matmul statement and the
    sorter (stream-family), its
    real source/extract/banlist/fourstate stages and a FAKE Lean that records the generated
    `Submission.Design`; a refusal fixture stops at `source`.
The real Lean side (the comparator's `--goal-arg`) is tests/checker/test_comparator.py.

    python3.12 tests/checker/test_clocked.py
"""
import glob
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
spec = importlib.util.spec_from_file_location("svgolf_check_py_clocked", os.path.join(SVGOLF, "check.py"))
checkpy = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = checkpy
spec.loader.exec_module(checkpy)
import srcgate  # noqa: E402

COUNTER = os.path.join(SVGOLF, "tests", "seq_counter")
CNT_SV = os.path.join(COUNTER, "reference", "cnt.sv")
MATMUL_SV = os.path.join(SVGOLF, "tasks", "matmul", "reference", "matmul_g1.sv")
SORTER = os.path.join(SVGOLF, "tasks", "sorter")
SORTER_SV = os.path.join(SORTER, "reference", "sorter_ins.sv")
ATTACKS = sorted(glob.glob(os.path.join(COUNTER, "attacks", "*.sv")))
MATMUL_TASK = {"name": "tx_matmul", "kind": "tx-family", "clock": "clk", "top": "matmul",
               "parameters": [{"name": n} for n in ("N", "W", "AccW")],
               "statement": {"module": "tasks.matmul.Spec", "constant": "SvGolf.Tasks.Matmul.Statement"},
               "probe_points": ["N=1,W=1,AccW=1", "N=2,W=3,AccW=5"],
               "scoring": {"params": {"N": 4, "W": 8, "AccW": 32}}}


class Gate(unittest.TestCase):
    def test_each_refusal_fixture_is_refused_for_its_one_rule(self):
        self.assertGreaterEqual(len(ATTACKS), 12)
        for path in ATTACKS:
            with open(path) as fh:
                want = fh.readline().removeprefix("// expect:").strip()
            canon, found = srcgate.gate_file(path, clock="clk")
            with self.subTest(os.path.basename(path)):
                self.assertIsNone(canon)
                self.assertEqual(len(found), 1, found)
                self.assertIn("clocked task: " + want, found[0])
                self.assertEqual(srcgate.gate_file(path)[1], [])      # the rules are clocked-only

    def test_the_counter_and_the_matmul_reference_pass(self):
        for path in (CNT_SV, MATMUL_SV):
            self.assertEqual(srcgate.gate_file(path, clock="clk")[1], [], path)

    def test_the_clock_is_the_tasks(self):
        (f,) = srcgate.gate_file(CNT_SV, clock="ck")[1]
        self.assertIn("clocked by `clk`: the task has exactly one clock, `ck`", f)


class Header(unittest.TestCase):
    def test_kinds(self):
        self.assertEqual(checkpy.task_kind({"kind": "seq-family", "clock": "clk"}), "seq-family")
        for bad in ({"kind": "seq-fam"}, {"kind": "tx-family", "parameters": [{"name": "N"}]},
                    {"kind": "tx-family", "clock": "clk"}):
            self.assertRaises(RuntimeError, checkpy.task_kind, bad)
        with open(os.path.join(SORTER, "task.json")) as fh:
            sorter = json.load(fh)
        self.assertEqual(checkpy.task_kind(sorter), "stream-family")
        for key, val in (("count", "M"), ("count", None), ("out_valid", None)):     # count names a parameter
            with self.subTest(key=key, val=val):
                self.assertRaises(RuntimeError, checkpy.task_kind,
                                  {**sorter, "protocol": {**sorter["protocol"], key: val}})

    def test_the_latency_line(self):
        self.assertEqual(checkpy.parse_latency("import X\n-- svgolf-latency: 5\n", "tx-family"), 5)
        self.assertEqual(checkpy.parse_latency("--svgolf-latency:12 \n", "tx-family"), 12)
        self.assertEqual(checkpy.parse_latency("-- svgolf-latency: 16\n", "stream-family"), 16)
        self.assertIsNone(checkpy.parse_latency("import X\n", "seq-family"))
        for text, kind in (("import X\n", "tx-family"), ("-- svgolf-latency: 0\n", "tx-family"),
                           ("-- svgolf-latency: 5 cycles\n", "tx-family"),
                           ("-- svgolf-latency: 05\n", "tx-family"),
                           ("-- svgolf-latency: 5\n-- svgolf-latency: 4\n", "tx-family"),
                           ("  -- svgolf-latency: 5\n", "tx-family"),
                           ("import X\n", "stream-family"),
                           ("-- svgolf-latency: 5\n", "seq-family")):
            with self.subTest(text=text, kind=kind):
                with self.assertRaises(checkpy.Reject) as cm:
                    checkpy.parse_latency(text, kind)
                self.assertEqual(cm.exception.stage, "latency")

    def test_the_goals(self):
        self.assertEqual(checkpy.goal_text(MATMUL_TASK, 9),
                         "abbrev Goal (lat : Nat → Nat → Nat → Nat) : Prop :=\n"
                         "  SvGolf.Tasks.Matmul.Statement design.sem lat ∧ lat 4 8 32 = 9")
        with open(os.path.join(COUNTER, "task.json")) as fh:
            self.assertEqual(checkpy.goal_text(json.load(fh)),
                             "abbrev Goal : Prop := SvGolf.Tests.SeqCounter.Statement design.sem")
        with open(os.path.join(SORTER, "task.json")) as fh:
            self.assertEqual(checkpy.goal_text(json.load(fh), 16),
                             "abbrev Goal (lat : Nat → Nat → Nat) : Prop :=\n"
                             "  SvGolf.Tasks.Sorter.Statement design.sem lat ∧ lat 8 8 = 16")

    def test_the_comparator_report_keeps_goal_arg_for_tx_only(self):
        def out(goal_arg):
            rep = {"accepted": True, "goal": "Submission.Goal", "goal_arg": goal_arg, "errors": []}
            return "noise\nSVGOLF_COMPARATOR " + json.dumps(rep) + "\n"
        # no goal argument (comb-family, comb-fixed, seq-family): the null key is dropped, so the
        # combinational result stays the byte-identity goldens' (tests/checker/ppa_wiring/)
        rep = checkpy.comparator_report(out(None))
        self.assertNotIn("goal_arg", rep)
        self.assertEqual(rep, {"accepted": True, "goal": "Submission.Goal", "errors": []})
        # tx-family (`--goal-arg Submission.lat`): kept
        rep = checkpy.comparator_report(out(checkpy.LATENCY_DEF), checkpy.LATENCY_DEF)
        self.assertEqual(rep["goal_arg"], "Submission.lat")
        # a non-null goal_arg the run did not ask for is never hidden
        self.assertEqual(checkpy.comparator_report(out("X.y"))["goal_arg"], "X.y")
        self.assertIsNone(checkpy.comparator_report("no report here"))


class FakeLean:
    """check.py's `Lean`: every compile succeeds with the design stage's marker, and is recorded."""
    compiled = []

    def __init__(self, stage, wrap):
        pass

    def run(self, args, timeout=None, lake_env=True, **kw):
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        with open(module_path) as fh:
            FakeLean.compiled.append(fh.read())
        return 0, "SVGOLF_UNSUPPORTED_FREE 3\n", 1.0


class Check(unittest.TestCase):
    def run_check(self, task_dir, sv, **kw):
        FakeLean.compiled = []
        stage = tempfile.mkdtemp(prefix="svgolf-clockedtest-")
        self.addCleanup(shutil.rmtree, stage, ignore_errors=True)
        orig, checkpy.Lean = checkpy.Lean, FakeLean
        try:
            return checkpy.check(task_dir, sv, None, stage, [], do_score=False, build_trusted=False,
                                 unproved=True, **kw)
        finally:
            checkpy.Lean = orig

    def test_the_counter_reaches_the_design_stage(self):
        res = self.run_check(COUNTER, CNT_SV)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual(res["stages"]["task"]["kind"], "seq-family")
        self.assertIn("abbrev Goal : Prop := SvGolf.Tests.SeqCounter.Statement design.sem",
                      FakeLean.compiled[0])

    def test_a_refusal_fixture_stops_at_source(self):
        res = self.run_check(COUNTER, os.path.join(COUNTER, "attacks", "async_reset.sv"))
        self.assertEqual(res["stage"], "source")
        self.assertIn("a second event", res["errors"][0])

    def test_a_tx_task_pins_the_declared_latency(self):
        tdir = tempfile.mkdtemp(prefix="svgolf-txtask-")
        self.addCleanup(shutil.rmtree, tdir, ignore_errors=True)
        with open(os.path.join(tdir, "task.json"), "w") as fh:
            json.dump(MATMUL_TASK, fh)
        res = self.run_check(tdir, MATMUL_SV, latency=5)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual(res["latency"], 5)
        self.assertIn("design.sem lat ∧ lat 4 8 32 = 5", FakeLean.compiled[0])
        with self.assertRaises(RuntimeError):            # --latency is for an unproved tx run only
            self.run_check(COUNTER, CNT_SV, latency=5)

    def test_a_stream_task_pins_the_declared_latency(self):
        res = self.run_check(SORTER, SORTER_SV, latency=16)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual((res["latency"], res["stages"]["task"]["kind"]), (16, "stream-family"))
        self.assertIn("SvGolf.Tasks.Sorter.Statement design.sem lat ∧ lat 8 8 = 16", FakeLean.compiled[0])
        with self.assertRaises(RuntimeError):            # an unproved stream run names its latency
            self.run_check(SORTER, SORTER_SV)


if __name__ == "__main__":
    unittest.main(verbosity=1)
