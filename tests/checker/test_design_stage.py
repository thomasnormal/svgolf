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
  * the marker is recorded as `stages.design.unsupported_free_points`.

The real Lean side is exercised by `tests/run.py` (the attacks `func_call`,
`assign_func`, `fn_uninit`, `latch_never` and `latch_star` of `tests/_example/attacks/`,
rejected at `design`, and every reference accepted).

    python3.12 tests/checker/test_design_stage.py
"""

import importlib.util
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


if __name__ == "__main__":
    unittest.main(verbosity=1)
