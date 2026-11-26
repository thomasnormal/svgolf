#!/usr/bin/env python3.12
"""check.py on an exploration task (kind `explore-stream`, tasks/gemm), no Lean: the stages of an `--unproved` run and
its result, what is refused before any simulation, and that nothing of it is ever accepted.

    python3.12 tests/checker/test_explore.py

The runs use `--no-score` (the composed score takes minutes: score/test_hier.py and tests/gemm/test_gemm.py test its
parts). The simulation needs Verilator; without it the run tests are SKIPPED.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
TASK = os.path.join(SVGOLF, "tasks", "gemm")
PAR = os.path.join(TASK, "reference", "par.sv")
PAR_DECL = os.path.join(TASK, "reference", "par.json")
sys.dont_write_bytecode = True
HAVE_SIM = shutil.which("verilator") is not None and shutil.which("make") is not None
needs_sim = unittest.skipUnless(HAVE_SIM, "needs Verilator 5, make and a C++ compiler")


def run_check(*args, timeout=1200):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    p = subprocess.run([sys.executable, os.path.join(SVGOLF, "check.py"), *args], capture_output=True, text=True,
                       timeout=timeout, env=env, cwd=SVGOLF)
    try:
        return p.returncode, json.loads(p.stdout), p.stderr
    except ValueError:
        return p.returncode, None, p.stdout + p.stderr


class Explore(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="svgolf-explore-check-")
        with open(PAR) as fh:
            cls.par = fh.read()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def design(self, name, old=None, new=None):
        text = self.par
        if old is not None:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        path = os.path.join(self.tmp, name)
        with open(path, "w") as fh:
            fh.write(text)
        return path

    @needs_sim
    def test_an_unproved_run_passes_every_stage_and_is_never_accepted(self):
        rc, res, err = run_check(TASK, PAR, "--unproved", "--declare", PAR_DECL, "--no-score")
        self.assertEqual(rc, 0, err)
        self.assertEqual((res["task"], res["stage"], res["accepted"], res["unproved_ok"], res["exploration"]),
                         ("gemm", "unproved", False, True, True))
        self.assertEqual(res["errors"], [])
        for stage in ("source", "declare", "extract", "banlist", "fourstate", "clocked_rules", "explore"):
            self.assertIn(stage, res["stages"])
        for stage in ("trusted", "design", "solution", "comparator", "ppa", "score", "hier"):
            self.assertNotIn(stage, res["stages"])                     # no Lean stage, and --no-score: no score
        self.assertNotIn("score", res)
        self.assertIsNone(res["stages"]["task"]["statement"])
        self.assertEqual(res["stages"]["extract"]["points"], ["LGE=2,LAT=3", "LGE=2,LAT=1", "LGE=3,LAT=2", "LGE=7,LAT=32"])
        self.assertEqual(res["stages"]["declare"]["layout"], "canonical")
        self.assertIn("nothing is proved and the design is not accepted", res["notes"][0])
        pts = res["stages"]["explore"]["points"]
        self.assertEqual(len(pts), 4)
        self.assertEqual(pts[3]["params"], {"LGE": 7, "LAT": 32})          # the scored parameters, short jobs
        self.assertIn("skipped", pts[3]["scored_job"])                 # the scored job's run comes with the score
        self.assertTrue(all(p["results"]["independence"] for p in pts))
        self.assertIn("skipped", pts[0]["netlist"])                    # the netlist comes with the score

    def test_a_proof_cannot_be_checked_against_a_task_without_a_statement(self):
        lean = os.path.join(self.tmp, "Solution.lean")
        with open(lean, "w") as fh:
            fh.write("import Submission.Design\n")
        rc, res, err = run_check(TASK, PAR, lean, "--no-score")
        self.assertEqual(rc, 2, err)
        self.assertEqual(res["stage"], "infrastructure")
        self.assertIn("has no trusted statement yet", res["errors"][0])

    def test_the_score_needs_a_cycle_formula(self):
        decl = os.path.join(self.tmp, "nocycles.json")
        with open(decl, "w") as fh:
            json.dump({"cycles": None, "layout": None}, fh)
        rc, res, err = run_check(TASK, PAR, "--unproved", "--declare", decl)
        self.assertEqual((rc, res["stage"]), (1, "declare"), err)
        self.assertIn("no cycle formula is declared", res["errors"][0])

    def test_a_bad_declaration_is_refused(self):
        decl = os.path.join(self.tmp, "bad.json")
        with open(decl, "w") as fh:
            json.dump({"cycles": "__import__('os').system('true')", "layout": None}, fh)
        rc, res, err = run_check(TASK, PAR, "--unproved", "--declare", decl, "--no-score")
        self.assertEqual((rc, res["stage"]), (1, "declare"), err)
        self.assertIn("the declared cycle formula", res["errors"][0])

    def test_another_port_width_is_refused_at_extract(self):
        sv = self.design("wide.sv", "  output logic [4:0]             y_row,", "  output logic [5:0]             y_row,")
        rc, res, err = run_check(TASK, sv, "--unproved", "--declare", PAR_DECL, "--no-score")
        self.assertEqual((rc, res["stage"]), (1, "extract"), err)
        self.assertIn("`y_row` is 6 bits wide, the task's is 5 bits", res["errors"][0])

    def test_another_parameter_is_refused_at_extract(self):
        sv = self.design("param.sv", "module gemm #(parameter int LGE = 2, parameter int LAT = 3) (",
                         "module gemm #(parameter int LGE = 2, parameter int LAT = 3, parameter int FAST = 0) (")
        rc, res, err = run_check(TASK, sv, "--unproved", "--declare", PAR_DECL, "--no-score")
        self.assertEqual((rc, res["stage"]), (1, "extract"), err)
        self.assertIn("must have exactly the parameters ['LGE', 'LAT']", res["errors"][0])

    def test_a_banned_operator_is_refused(self):
        sv = self.design("div.sv", "            lgq   <= 3'(job_lgn - 4'(LGE));",
                         "            lgq   <= 3'((job_lgn - 4'(LGE)) / job_lgn[1:0]);")
        rc, res, err = run_check(TASK, sv, "--unproved", "--declare", PAR_DECL, "--no-score")
        self.assertEqual((rc, res["stage"]), (1, "banlist"), err)

    def test_declare_is_for_exploration_tasks_only(self):
        rc, res, err = run_check(os.path.join(SVGOLF, "tasks", "arbiter"),
                                 os.path.join(SVGOLF, "tasks", "arbiter", "reference", "rr_mask.sv"), "--unproved",
                                 "--declare", PAR_DECL, "--no-score", "--no-trusted-build")
        self.assertEqual(rc, 2, err)
        self.assertIn("--declare is for an exploration task", res["errors"][0])


if __name__ == "__main__":
    unittest.main()
