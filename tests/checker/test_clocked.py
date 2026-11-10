#!/usr/bin/env python3.12
"""The clocked checker's front end (PLAN4 Gate 2, steps 1 and 2), without Lean:

  * the source gate's clocked rules (score/srcgate.py item 6): every refusal fixture of
    `tests/seq_counter/attacks/` (one rule each, its first line `// expect: <message>`) is refused
    with exactly that one finding under the task's clock, and passes the combinational gate; the
    counter (`tests/seq_counter/reference/cnt.sv`) and the matmul reference pass the clocked gate;
  * the kinds (`task_kind`), the latency header (`parse_latency`) and the generated goal
    (`goal_text`: `Statement design.sem lat ∧ lat p₀ = n` for tx-family and stream-family,
    `Statement design.sem` for seq-family and react-family);
  * check.py itself on the counter task, a tx-family task built on the matmul statement and the
    sorter (stream-family) and the arbiter (react-family), its
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
from unittest import mock

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
ARBITER = os.path.join(SVGOLF, "tasks", "arbiter")
ARBITER_SV = os.path.join(ARBITER, "reference", "rr_mask.sv")
ATTACKS = sorted(glob.glob(os.path.join(COUNTER, "attacks", "*.sv")))
MATMUL_TASK = {"name": "tx_matmul", "kind": "tx-family", "clock": "clk", "top": "matmul",
               "parameters": [{"name": n} for n in ("N", "W", "AccW")],
               "statement": {"module": "tasks.matmul.Spec", "constant": "SvGolf.Tasks.Matmul.Statement"},
               "probe_points": ["N=1,W=1,AccW=1", "N=2,W=3,AccW=5"],
               "scoring": {"params": {"N": 4, "W": 8, "AccW": 32}},
               "ports": json.load(open(os.path.join(SVGOLF, "tasks", "matmul", "task.json")))["ports"]}


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
        with open(os.path.join(ARBITER, "task.json")) as fh:
            arbiter = json.load(fh)
        self.assertEqual(checkpy.task_kind(arbiter), "react-family")
        self.assertIn("react-family", checkpy.CLOCKED_KINDS)          # the clocked source rules apply
        self.assertNotIn("react-family", checkpy.LATENCY_KINDS)       # no latency: one decision per cycle
        for bad in ({k: v for k, v in arbiter.items() if k != "reset"}, {**arbiter, "reset": {"level": 1}},
                    {**arbiter, "reset": {"port": "rst", "level": 2}}, {k: v for k, v in arbiter.items() if k != "clock"}):
            self.assertRaises(RuntimeError, checkpy.task_kind, bad)

    def test_the_latency_line(self):
        self.assertEqual(checkpy.parse_latency("import X\n-- svgolf-latency: 5\n", "tx-family"), 5)
        self.assertEqual(checkpy.parse_latency("--svgolf-latency:12 \n", "tx-family"), 12)
        self.assertEqual(checkpy.parse_latency("-- svgolf-latency: 16\n", "stream-family"), 16)
        self.assertIsNone(checkpy.parse_latency("import X\n", "seq-family"))
        self.assertIsNone(checkpy.parse_latency("import X\n", "react-family"))
        for text, kind in (("import X\n", "tx-family"), ("-- svgolf-latency: 0\n", "tx-family"),
                           ("-- svgolf-latency: 5 cycles\n", "tx-family"),
                           ("-- svgolf-latency: 05\n", "tx-family"),
                           ("-- svgolf-latency: 5\n-- svgolf-latency: 4\n", "tx-family"),
                           ("  -- svgolf-latency: 5\n", "tx-family"),
                           ("import X\n", "stream-family"),
                           ("-- svgolf-latency: 5\n", "seq-family"),
                           ("-- svgolf-latency: 1\n", "react-family")):
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
        with open(os.path.join(ARBITER, "task.json")) as fh:
            self.assertEqual(checkpy.goal_text(json.load(fh)),
                             "abbrev Goal : Prop := SvGolf.Tasks.Arbiter.Statement design.sem")

    def test_the_latency_at_every_point(self):
        """F8 (decided 2026-11-08): the clocked points (the task's `postsynth.points`, the scoring point first when they
        do not list it), `--latency-at POINT:n`, an `--unproved` run's latency per point (the scoring point's n where
        none is given), and a proved run's from the comparator's `goal_arg_at` (Comparator point 8)."""
        with open(os.path.join(SORTER, "task.json")) as fh:
            sorter = json.load(fh)
        self.assertEqual(checkpy.clocked_points(sorter), [{"N": 3, "W": 4}, {"N": 8, "W": 8}])
        other = dict(sorter, scoring={"params": {"N": 4, "W": 8}})
        self.assertEqual(checkpy.clocked_points(other), [{"N": 4, "W": 8}, {"N": 3, "W": 4}, {"N": 8, "W": 8}])
        self.assertEqual(checkpy.parse_latency_at(["N=3,W=4:6", " N=8, W=8 : 16", "N=3,W=4:6"]),
                         {"N=3,W=4": 6, "N=8,W=8": 16})
        self.assertEqual(checkpy.parse_latency_at(None), {})
        for bad in (["N=3,W=4"], ["N=3,W=4:0"], ["N=3,W=4:x"], ["N=3,W=4:06"], ["N=3,W=4:6", "N=3,W=4:7"]):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                checkpy.parse_latency_at(bad)
        self.assertEqual(checkpy.unproved_latency_at(sorter, 16, {}), {"N=3,W=4": 16, "N=8,W=8": 16})
        self.assertEqual(checkpy.unproved_latency_at(sorter, 16, {"N=3,W=4": 6, "N=8,W=8": 16}),
                         {"N=3,W=4": 6, "N=8,W=8": 16})
        for given in ({"N=4,W=8": 8}, {"N=8,W=8": 15}):
            with self.subTest(given=given), self.assertRaises(RuntimeError):
                checkpy.unproved_latency_at(sorter, 16, given)

        def comp(*entries):
            return {"goal_arg_at": [dict(args=a, **e) for a, e in entries]}
        ok = comp(([3, 4], {"value": 6}), ([8, 8], {"value": 16}))
        self.assertEqual(checkpy.latency_at_from_comparator(sorter, ok, 16), {"N=3,W=4": 6, "N=8,W=8": 16})
        for c, stage in ((comp(([3, 4], {"error": "not a number"}), ([8, 8], {"value": 16})), "latency"),
                         (comp(([3, 4], {"value": 0}), ([8, 8], {"value": 16})), "latency"),
                         (comp(([3, 4], {"value": True}), ([8, 8], {"value": 16})), "latency"),
                         (comp(([3, 4], {"value": checkpy.LATENCY_MAX + 1}), ([8, 8], {"value": 16})), "latency"),
                         (comp(([3, 4], {"value": 6}), ([8, 8], {"value": 15})), None),     # the scoring point is n
                         (comp(([3, 4], {"value": 6})), None),                               # a point unanswered
                         (comp(([4, 3], {"value": 6}), ([8, 8], {"value": 16})), None),     # another point
                         ({}, None)):
            with self.subTest(comp=c):
                if stage is None:
                    self.assertRaises(RuntimeError, checkpy.latency_at_from_comparator, sorter, c, 16)
                else:
                    with self.assertRaises(checkpy.Reject) as cm:
                        checkpy.latency_at_from_comparator(sorter, c, 16)
                    self.assertEqual(cm.exception.stage, stage)

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

    def test_the_arbiter_reaches_the_design_stage_under_the_clocked_rules(self):
        res = self.run_check(ARBITER, ARBITER_SV)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual((res["stages"]["task"]["kind"], res.get("latency")), ("react-family", None))
        self.assertIn("abbrev Goal : Prop := SvGolf.Tasks.Arbiter.Statement design.sem", FakeLean.compiled[0])
        # the clocked source rules: an asynchronous reset (the loader would drop it: design/reactive H2)
        res = self.run_check(ARBITER, os.path.join(SVGOLF, "tests", "arbiter", "attacks", "a13_async.sv"))
        self.assertEqual(res["stage"], "source")
        self.assertIn("a second event", res["errors"][0])
        with self.assertRaises(RuntimeError):            # no latency for a reactive task
            self.run_check(ARBITER, ARBITER_SV, latency=1)

    def test_a_stream_task_pins_the_declared_latency(self):
        res = self.run_check(SORTER, SORTER_SV, latency=16)
        self.assertEqual(res["stage"], "unproved", res["errors"])
        self.assertEqual((res["latency"], res["stages"]["task"]["kind"]), (16, "stream-family"))
        self.assertIn("SvGolf.Tasks.Sorter.Statement design.sem lat ∧ lat 8 8 = 16", FakeLean.compiled[0])
        with self.assertRaises(RuntimeError):            # an unproved stream run names its latency
            self.run_check(SORTER, SORTER_SV)


class Integrity(unittest.TestCase):
    """The clocked kinds' trusted files (check.py CLOCKED_TRUSTED: score/svgolf_seq.ys, score/ge_seq.json,
    check/clocked_rules.py, 2026-11-07) are fingerprinted BY CONTENT by the integrity tripwire (`integrity_snapshot`):
    an edit of one between two snapshots is a difference, and nothing else is (on copies of the three files: the
    real ones are the checker's); and a record names their hashes (leaderboard.py CHECKER_FILES)."""

    def snapshot(self, root, stage):
        with mock.patch.object(checkpy, "SVGOLF", root), mock.patch.object(checkpy, "LS_ROOT", os.path.dirname(root)), \
                mock.patch.object(checkpy, "_tool_trees", return_value=[]), \
                mock.patch.object(checkpy.postsynth, "trusted_files",
                                  side_effect=checkpy.postsynth.InfraError("none here")):
            return checkpy.integrity_snapshot(stage)

    def test_an_edit_of_a_clocked_file_is_caught(self):
        tmp = tempfile.mkdtemp(prefix="svgolf-clocked-trip-")
        self.addCleanup(shutil.rmtree, tmp, ignore_errors=True)
        root, stage = os.path.join(tmp, "svgolf"), os.path.join(tmp, "stage")
        os.makedirs(stage)
        paths = []
        for parts in checkpy.CLOCKED_TRUSTED:
            os.makedirs(os.path.join(root, *parts[:-1]), exist_ok=True)
            paths.append(os.path.join(root, *parts))
            shutil.copyfile(os.path.join(SVGOLF, *parts), paths[-1])
        self.assertEqual(sorted("/".join(p) for p in checkpy.CLOCKED_TRUSTED),
                         ["check/clocked_rules.py", "score/ge_seq.json", "score/svgolf_seq.ys"])
        before = self.snapshot(root, stage)
        for p in paths:
            self.assertEqual(before.get(p), "sha256:" + checkpy.sha256_file(p), p)
        self.assertEqual(checkpy.integrity_diff(before, self.snapshot(root, stage)), [])
        for p in paths:
            with open(p, "rb") as fh:
                orig = fh.read()
            with open(p, "ab") as fh:
                fh.write(b"\n# a solution's build edited this\n")
            self.assertEqual(checkpy.integrity_diff(before, self.snapshot(root, stage)), [p])
            with open(p, "wb") as fh:
                fh.write(orig)
        self.assertEqual(checkpy.integrity_diff(before, self.snapshot(root, stage)), [])

    def test_a_record_names_their_hashes(self):
        spec = importlib.util.spec_from_file_location("svgolf_lb_clocked", os.path.join(SVGOLF, "leaderboard",
                                                                                          "leaderboard.py"))
        lb = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(lb)
        hashes = lb.checker_file_hashes()
        for parts in checkpy.CLOCKED_TRUSTED:
            rel = "/".join(parts)
            self.assertIn(rel, lb.CHECKER_FILES)
            self.assertEqual(hashes.get(rel), checkpy.sha256_file(os.path.join(SVGOLF, rel)), rel)


class Ports(unittest.TestCase):
    """The `extract` stage's port check (check.py `port_problems`, 2026-11-07, every kind): the ports of the
    extractor's view at each probe point (the sidecar's; the envelope's module at the defaults when a task has
    none) against task.json `ports`, as the statement's `Interface` reads them: the inputs in declaration order
    with their widths, the outputs likewise, no other direction; a view with an `Unsupported` port is left to the
    `design` stage. On synthetic views (the real extractor's runs: tests/run.py, the negatives and attacks)."""
    TASK = {"ports": {"inputs": [{"name": "clk", "width": "1"}, {"name": "rst", "width": "1"},
                                 {"name": "req", "width": "N"}],
                      "outputs": [{"name": "gnt", "width": "N"}]}}

    @staticmethod
    def port(name, d, w):
        return {"kind": "Port", "name": name, "dir": d, "width": {"kind": "PackedType", "resolved": w}}

    def problems(self, ports_at, task=None):
        tmp = tempfile.mkdtemp(prefix="svgolf-ports-")
        self.addCleanup(shutil.rmtree, tmp, ignore_errors=True)
        side = os.path.join(tmp, "d.probes.json")
        with open(side, "w") as fh:
            json.dump({"points": [{"overrides": [{"name": "N", "value": n}],
                                   "module": {"name": "arbiter", "ports": ports}}
                                  for n, ports in ports_at.items()]}, fh)
        return checkpy.port_problems(task or self.TASK, "arbiter", None, side)

    def good(self, n):
        return [self.port("clk", "in", 1), self.port("rst", "in", 1), self.port("req", "in", n),
                self.port("gnt", "out", n)]

    def test_the_widths_are_expressions_of_the_parameters(self):
        self.assertEqual(checkpy.port_width("N*N*W", {"N": 4, "W": 8}), 128)
        self.assertEqual(checkpy.port_width("2*N-1", {"N": 16}), 31)
        self.assertEqual(checkpy.port_width("(W+P)", {"W": 5, "P": 11}), 16)
        for bad in ("N**2", "M", "N/2", "len(N)", "N +"):
            with self.subTest(bad), self.assertRaises(RuntimeError):
                checkpy.port_width(bad, {"N": 2})

    def test_the_tasks_ports_pass_at_every_point(self):
        self.assertEqual(self.problems({1: self.good(1), 8: self.good(8)}), ([], ["N=1", "N=8"]))

    def test_a_wider_port_another_order_an_extra_port_or_an_inout_is_refused(self):
        wide = self.good(1)[:2] + [self.port("req", "in", 2), self.port("gnt", "out", 1)]
        (bad,), _ = self.problems({1: wide, 8: self.good(8)})
        self.assertEqual(bad, "at N=1: input `req` is 2 bits wide, the task's is 1 bit")
        swapped = [self.port("rst", "in", 1), self.port("clk", "in", 1)] + self.good(3)[2:]
        self.assertIn("the inputs are ['rst', 'clk', 'req'] (in declaration order), the task's are "
                      "['clk', 'rst', 'req']", self.problems({3: swapped})[0][0])
        extra = self.good(3) + [self.port("busy", "out", 1)]
        self.assertIn("the outputs are ['gnt', 'busy']", self.problems({3: extra})[0][0])
        inout = self.good(3)[:3] + [self.port("gnt", "inout", 3)]
        self.assertIn("port `gnt` is `inout`", self.problems({3: inout})[0][0])
        # an output interleaved with the inputs in declaration order is still the task's (Interface filters by
        # direction)
        mixed = [self.port("clk", "in", 1), self.port("gnt", "out", 3), self.port("rst", "in", 1),
                 self.port("req", "in", 3)]
        self.assertEqual(self.problems({3: mixed})[0], [])

    def test_an_unsupported_port_is_left_to_the_design_stage(self):
        ports = self.good(3)[:3] + [{"kind": "Unsupported", "sv_kind": "PortSymbol:net-z", "text": "gnt"}]
        self.assertEqual(self.problems({3: ports}), ([], []))

    def test_a_task_without_probe_points_is_checked_at_the_defaults(self):
        task = {"ports": {"inputs": [{"name": "x", "width": "8"}], "outputs": [{"name": "y", "width": "8"}]}}
        envl = {"design": {"modules": [{"name": "aes_sbox", "params": [],
                                        "ports": [self.port("a", "in", 8), self.port("y", "out", 8)]}]}}
        bad, judged = checkpy.port_problems(task, "aes_sbox", envl, None)
        self.assertEqual((bad, judged), (["at the defaults: the inputs are ['a'] (in declaration order), the task's "
                                          "are ['x']"], ["the defaults"]))


if __name__ == "__main__":
    unittest.main(verbosity=1)
