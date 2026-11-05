#!/usr/bin/env python3.12
"""A program slang reports illegal is rejected, also for a task with an EMPTY banlist (WP-RB1), without Lean:
`check.py`'s real source / extract / banlist / fourstate stages (pyslang, the extractor and Yosys) run on a design with a
slang ERROR that the source gate does not see, and the Lean runner is a fake (as in test_design_stage.py).

  * `banlist.check` with no banned operator returns `passed` BEFORE it compiles anything, and `check.py` skips the
    banlist front check (`if ops:`): that is the hole, and the premise of the pin below (if it is ever closed, this
    file says so and the pin can move);
  * the `fourstate` stage ALWAYS runs and reads slang's diagnostics: the design is rejected there, under its own
    header ("slang reports the program illegal at the scoring point"), not under the x/z header;
  * with the task's banlist non-empty the same design is rejected earlier, at `banlist`;
  * a legal design passes both stages with an empty banlist (the pin is not a blanket refusal).

The error is an unused `localparam int UNUSED = UNDEFINED_NAME;`: slang rejects it (UndeclaredIdentifier), Yosys reads the
program without a finding, so nothing but slang's own report stands between the program and the proof.
See svgolf/design/real-world-sv/rb0/ENVELOPE-ERRORS.md.

    python3.12 tests/checker/test_slang_errors.py
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


checkpy = load("svgolf_check_py_slang_errors", os.path.join(SVGOLF, "check.py"))
import banlist  # noqa: E402  (score/banlist.py)
import fourstate  # noqa: E402  (score/fourstate.py)

TASK = os.path.join(SVGOLF, "tasks", "_example")
with open(os.path.join(TASK, "reference", "band.sv")) as _fh:
    LEGAL = _fh.read()
ILLEGAL = LEGAL.replace("  assign y = a & b;", "  assign y = a & b;\n  localparam int UNUSED = UNDEFINED_NAME;")


class FakeLean:
    """Stands in for check.py's `Lean`; the design stage answers what a clean design gets."""

    def __init__(self, stage, wrap):
        self.stage, self.wrap = stage, wrap

    def run(self, args, timeout=None, lake_env=True, **kw):
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        return 0, "SVGOLF_UNSUPPORTED_FREE 4\n", 1.0


class SlangErrorsAtTheChecker(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="svgolf-slang-errors-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        # a copy of the toy task whose banlist is EMPTY
        self.empty = os.path.join(self.tmp, "band_nobans")
        shutil.copytree(TASK, self.empty)
        path = os.path.join(self.empty, "task.json")
        with open(path) as fh:
            task = json.load(fh)
        task["banlist"]["operators"] = []
        with open(path, "w") as fh:
            json.dump(task, fh, indent=1)
        self.n = 0

    def design(self, text):
        self.n += 1       # a fresh path per text: pyslang caches source files by path for the whole process
        p = os.path.join(self.tmp, "d%d.sv" % self.n)
        with open(p, "w") as fh:
            fh.write(text)
        return p

    def run_check(self, task, sv):
        stage = os.path.join(self.tmp, "stage%d" % self.n)
        orig = checkpy.Lean
        checkpy.Lean = FakeLean
        try:
            return checkpy.check(task, sv, None, stage, [], do_score=False, build_trusted=False, unproved=True)
        finally:
            checkpy.Lean = orig

    def test_premise_the_banlist_check_with_no_operator_does_not_look_at_the_design(self):
        res = banlist.check([self.design(ILLEGAL)], "band", [], [], gate=False)
        self.assertTrue(res["passed"])
        self.assertEqual(res["diagnostics"], [])

    def test_premise_the_program_really_is_illegal_for_slang_and_clean_for_yosys(self):
        sv = self.design(ILLEGAL)
        front, diags = banlist.front_check([sv], "band", ["+"], [])
        self.assertEqual(front, [])
        self.assertEqual(len(diags), 1)
        self.assertIn("slang error", diags[0])
        self.assertIn("UndeclaredIdentifier", diags[0])
        res = fourstate.check([sv], "band", {"N": 16})
        self.assertEqual(res["findings"], [])                      # Yosys and the x/z rules have nothing to say
        self.assertEqual(len(res["diagnostics"]), 1)

    def test_an_illegal_program_is_rejected_at_fourstate_for_a_task_with_an_empty_banlist(self):
        res = self.run_check(self.empty, self.design(ILLEGAL))
        self.assertEqual((res["accepted"], res["stage"]), (False, "fourstate"))
        (err,) = res["errors"]
        self.assertTrue(err.startswith("slang reports the program illegal at the scoring point"), err)
        self.assertIn("slang error UndeclaredIdentifier", err)
        self.assertNotIn("an x or z value can arise", err)         # the wording: a slang error is not an x/z finding
        banlist_stage = res["stages"]["banlist"]
        self.assertEqual((banlist_stage["operators"], banlist_stage["diagnostics"]), ([], []))   # it got past the banlist
        self.assertNotIn("design", res["stages"])                  # and never reached Lean

    def test_the_same_program_is_rejected_earlier_when_the_banlist_is_not_empty(self):
        res = self.run_check(TASK, self.design(ILLEGAL))
        self.assertEqual((res["accepted"], res["stage"]), (False, "banlist"))
        self.assertIn("UndeclaredIdentifier", res["errors"][0])

    def test_a_legal_program_passes_both_stages_with_an_empty_banlist(self):
        res = self.run_check(self.empty, self.design(LEGAL))
        self.assertEqual(res["stage"], "unproved")                 # past banlist and fourstate, at the (fake) design stage
        self.assertEqual(res["stages"]["fourstate"]["diagnostics"], [])
        self.assertTrue(res["stages"]["fourstate"]["passed"])

    def test_a_genuine_x_finding_keeps_the_x_header(self):
        # an undriven output is a fourstate FINDING (no slang error): the old wording stays for it
        undriven = LEGAL.replace("  assign y = a & b;", "  assign y[0] = a[0] & b[0];")
        res = self.run_check(self.empty, self.design(undriven))
        self.assertEqual((res["accepted"], res["stage"]), (False, "fourstate"))
        self.assertTrue(res["errors"][0].startswith("an x or z value can arise"), res["errors"][0])


if __name__ == "__main__":
    unittest.main(verbosity=1)
