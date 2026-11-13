#!/usr/bin/env python3.12
"""`check.py --lift-banlist` (decided 2026-11-12: every design the site shows has a kernel-checked proof, the comparison
designs that use an operator the task bans included), without Lean: check.py's real source, extract, banlist and
fourstate stages run (pyslang, the extractor, Yosys) on task `add`'s banned baseline `tests/add/negative/plus.sv`
(`{cout, s} = a + b + cin`), and the Lean runner is a fake (tests/checker/test_design_stage.py's) whose design, solution,
comparator and leanchecker runs succeed:

  * WITHOUT the option the banlist rejects the design at stage `banlist`, as before, and no Lean stage runs;
  * WITH it the design passes the banlist stage (only the run-time / % ** every task bans are checked) and reaches the
    proof stages: the solution is compiled, the comparator and the kernel replay run; the result is NEVER accepted,
    stops at the pseudo-stage `lifted` with `lifted_ok`, says "banned operator: proved, not an entry", and records the
    task banlist's own verdict (`rejects`, with its findings) in `banlist_lifted`;
  * with it a design that uses a run-time `/` (banned in every task) is still rejected at `banlist`;
  * a lifted result can never become a record: `leaderboard.py`'s `acceptance_problems` refuses it, and `add
    --from-check` (in a trial data directory) refuses it and writes nothing; `--unproved --lift-banlist` (the fast loop
    a prover stages a design with) is clean and carries the same marker.

The real Lean side is `tests/run.py`'s step `baseline-proofs`, which checks every proved baseline with its proof.

    python3.12 tests/checker/test_lift_banlist.py
"""

import importlib.util
import json
import os
import shutil
import subprocess
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


checkpy = load("svgolf_check_py_lift", os.path.join(SVGOLF, "check.py"))
lb = load("svgolf_leaderboard_lift", os.path.join(SVGOLF, "leaderboard", "leaderboard.py"))
TASK = os.path.join(SVGOLF, "tasks", "add")
PLUS = os.path.join(SVGOLF, "tests", "add", "negative", "plus.sv")
LEAN = os.path.join(TASK, "reference", "add_n.lean")     # any proof file: the fake Lean compiles nothing
DIV_SV = """module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  assign s = a / (b | 1);
  assign cout = cin;
endmodule
"""


def solution_imports(path):
    with open(path) as fh:
        return ["Init"] + [ln.split()[1] for ln in fh if ln.startswith("import ")]


class FakeLean:
    """check.py's `Lean`, faked: every compile and run succeeds; the comparator reports an accepted theorem with the
    standard axioms. `ran` lists what was run, in order."""
    ran = []

    def __init__(self, stage, wrap):
        self.stage, self.wrap = stage, wrap
        self.progress, self.usage = None, {"wall_s": 1.0, "cpu_s": 1.0, "stopped_by": None}

    def run(self, args, timeout=None, lake_env=True, **kw):
        FakeLean.ran.append(" ".join(args[:2]))
        if args[:2] == ["printenv", "LEAN_PATH"]:
            return 0, os.path.join(self.stage, "build") + "\n", 0.1
        if args[:2] == ["lean", "--run"]:
            rep = {"accepted": True, "axioms": ["propext", "Classical.choice", "Quot.sound"], "errors": [],
                   "goal": "Submission.Goal", "imports": {"Submission.Solution": solution_imports(LEAN)}}
            return 0, "SVGOLF_COMPARATOR " + json.dumps(rep) + "\n", 1.0
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        FakeLean.ran.append("compile " + os.path.basename(module_path))
        if os.path.basename(module_path) == "Design.lean":
            return 0, "SVGOLF_UNSUPPORTED_FREE 6\n", 1.0
        return 0, "", 1.0


def run_check(sv, lean, lift, unproved=False):
    FakeLean.ran = []
    stage = tempfile.mkdtemp(prefix="svgolf-lifttest-")
    orig = checkpy.Lean
    checkpy.Lean = FakeLean
    try:
        return checkpy.check(TASK, sv, lean, stage, [], do_score=False, build_trusted=False, unproved=unproved,
                             lift_banlist=lift)
    finally:
        checkpy.Lean = orig
        shutil.rmtree(stage, ignore_errors=True)


class LiftBanlist(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plain = run_check(PLUS, LEAN, lift=False)
        cls.plain_ran = list(FakeLean.ran)
        cls.lifted = run_check(PLUS, LEAN, lift=True)
        cls.lifted_ran = list(FakeLean.ran)

    def test_without_the_option_the_banlist_rejects_as_before(self):
        res = self.plain
        self.assertEqual((res["accepted"], res["stage"]), (False, "banlist"))
        self.assertIn("banned run-time operators", res["errors"][0])
        self.assertIn("+", " ".join(res["stages"]["banlist"]["front"] + res["stages"]["banlist"]["backstop"]))
        self.assertEqual(res["stages"]["banlist"]["operators"], ["+", "-", "*", "/", "%", "**"])
        self.assertNotIn("banlist_lifted", res)
        self.assertNotIn("lifted", res["stages"]["banlist"])
        self.assertEqual(self.plain_ran, [])                  # no Lean stage ran
        for k in ("design", "solution", "comparator", "leanchecker"):
            self.assertNotIn(k, res["stages"])

    def test_with_the_option_the_design_reaches_the_proof_stages(self):
        res = self.lifted
        st = res["stages"]
        self.assertEqual(st["banlist"]["operators"], ["/", "%", "**"])      # ALWAYS_BANNED only
        self.assertEqual((st["banlist"]["front"], st["banlist"]["backstop"], st["banlist"]["diagnostics"]), ([], [], []))
        for k in ("fourstate", "design", "solution", "integrity", "comparator", "leanchecker"):
            self.assertIn(k, st, k)
        self.assertEqual(st["solution"]["exit"], 0)
        self.assertTrue(st["comparator"]["result"]["accepted"])
        self.assertIn("compile Solution.lean", self.lifted_ran)
        self.assertIn("lean --run", self.lifted_ran)
        self.assertIn("leanchecker Submission.Design", self.lifted_ran)

    def test_the_result_is_never_accepted_and_says_why(self):
        res = self.lifted
        self.assertIs(res["accepted"], False)
        self.assertEqual((res["stage"], res["lifted_ok"], res["errors"]), ("lifted", True, []))
        self.assertNotIn("complete", res)
        (note,) = res["notes"]
        self.assertTrue(note.startswith("banned operator: proved, not an entry"), note)
        self.assertIn("lifted: + - *", note)
        lifted = res["banlist_lifted"]
        self.assertEqual(lifted, res["stages"]["banlist"]["lifted"])
        self.assertEqual((lifted["operators"], lifted["task_banlist"], lifted["verdict"]),
                         (["+", "-", "*"], "rejects", "banned operator: proved, not an entry"))
        self.assertEqual(lifted["task_operators"], self.plain["stages"]["banlist"]["operators"])
        self.assertTrue(any("+" in f for f in lifted["task_findings"]), lifted["task_findings"])

    def test_the_operators_every_task_bans_stay_banned(self):
        with tempfile.TemporaryDirectory(prefix="svgolf-lifttest-div-") as d:
            sv = os.path.join(d, "div.sv")
            with open(sv, "w") as fh:
                fh.write(DIV_SV)
            res = run_check(sv, LEAN, lift=True)
        self.assertEqual((res["accepted"], res["stage"]), (False, "banlist"))
        self.assertIn("/", " ".join(res["stages"]["banlist"]["front"] + res["stages"]["banlist"]["backstop"]))
        self.assertNotIn("lifted_ok", res)
        self.assertIn("banlist_lifted", res)              # the marker is there from the banlist stage on

    def test_the_unproved_fast_loop_runs_on_the_lifted_banlist(self):
        res = run_check(PLUS, None, lift=True, unproved=True)
        self.assertEqual((res["accepted"], res["stage"], res.get("unproved_ok")), (False, "unproved", True))
        self.assertEqual(res["banlist_lifted"]["task_banlist"], "rejects")
        self.assertTrue(any(n.startswith("--lift-banlist: the task's operator banlist was lifted")
                            for n in res["notes"]), res["notes"])

    def test_a_lifted_result_can_never_become_a_record(self):
        task = lb.load_task(lb.DEFAULT_TASKS, "add")
        with open(PLUS, "rb") as fh:
            sha = lb.sha256_bytes(fh.read())
        problems = lb.acceptance_problems(self.lifted, task, sha)
        self.assertTrue(any("check.py --lift-banlist" in p for p in problems), problems)
        self.assertTrue(any("did not accept" in p for p in problems), problems)
        # also when it is dressed up as an accepted, complete result
        dressed = json.loads(json.dumps(self.lifted))
        dressed.update(accepted=True, stage="done", complete=True)
        problems = lb.acceptance_problems(dressed, task, sha)
        self.assertTrue(any("check.py --lift-banlist" in p for p in problems), problems)
        self.assertTrue(any("did not check every operator the task bans" in p for p in problems), problems)

    def test_add_from_check_refuses_it_and_writes_nothing(self):
        with tempfile.TemporaryDirectory(prefix="svgolf-lifttest-lb-") as d:
            res_path = os.path.join(d, "lifted.json")
            data = os.path.join(d, "data")
            os.makedirs(data)
            dressed = json.loads(json.dumps(self.lifted))
            dressed.update(accepted=True, stage="done", complete=True)     # even dressed up
            with open(res_path, "w") as fh:
                json.dump(dressed, fh)
            proc = subprocess.run([sys.executable, os.path.join(SVGOLF, "leaderboard", "leaderboard.py"), "add",
                                   "--task", "add", "--sv", PLUS, "--lean", LEAN, "--player", "someone",
                                   "--from-check", res_path, "--data-dir", data, "--date", "2026-11-12"],
                                  capture_output=True, text=True, cwd=SVGOLF)
            self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
            self.assertIn("REFUSED", proc.stderr)
            self.assertIn("check.py --lift-banlist", proc.stderr)
            self.assertEqual([f for _, _, fs in os.walk(data) for f in fs], [])

    def test_the_command_line_takes_the_option_and_exits_0_on_a_clean_lifted_run(self):
        """main's exit status: 0 for a clean lifted run, as for a clean --unproved one; the headline says not
        rankable (checked on a hand-made result: main itself runs Lean)."""
        res = dict(self.lifted)
        self.assertTrue(res["lifted_ok"])
        self.assertIn("--lift-banlist", checkpy.__doc__)
        res["stages"] = dict(res["stages"], ppa={"seconds": 0.1})
        res["ppa"] = {"available": True, "area_um2_sky130": 497.9776, "area_e4um2_sky130": 4979776,
                      "delay_ps_sky130": 3143}
        res["score"] = {}
        line = checkpy.ranked_headline(res)
        self.assertTrue(line.startswith("not rankable, banned operator (sky130 A0'): 497.9776 um^2 x 3143 ps"), line)


if __name__ == "__main__":
    unittest.main(verbosity=1)
