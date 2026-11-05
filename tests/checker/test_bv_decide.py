#!/usr/bin/env python3.12
"""`check/Comparator.lean`, point 6 (WP-BV, 2026-11-01): `bv_decide` axioms are re-verified, on a hand-built
module chain with real Lean and nothing from Mathlib, the staging tree or the checker's own modules.

DORMANT GROUNDWORK. It was ruled on 2026-11-01 that external solvers are not supported, so `check.py` never passes
`--bv-decide` (its `BV_DECIDE_SUPPORTED` is False). These tests pass the flag themselves, to keep the re-verification
working for the day the support is switched on; the last one pins what `check.py` actually gets: without the flag
every `bv_decide` axiom is rejected, by a message that names the policy.

A `bv_decide` proof ends in an axiom `<decl>._native.bv_decide.ax_<i>_<j> : verifyBVExpr E C = true`
(E, C constants: a closed `BVLogicalExpr` constructor term and the LRAT certificate string). The comparator
decodes E from its kernel value, checks that the toolchain's `toExpr` of the decoded value is exactly that
value, and runs the toolchain's compiled `verifyBVExpr` on it. The cases:

  ACCEPTED   a real `bv_decide` proof (one axiom, two axioms, an axiom behind a helper lemma); the report
             lists each verified axiom; a hand-written axiom with the generated name and a TRUE statement
             (the real pair, re-declared: it is a true theorem whatever its source, which is why accepting
             it costs nothing; the NAME is a label, the evaluation is the check)
  REJECTED   a forged axiom over a false certificate (the attack the old refusal existed for: the
             axiom proves `False`); a right-named axiom of another type (`= false`, `False`, inline
             operands); a generated-shape axiom under another name; a TRUE statement whose formula is
             not literally a `toExpr` value (`id E`) or whose certificate is not a string literal; a
             shared term that exceeds the decoding budget; a term nested deeper than the limit;
             `Lean.ofReduceBool`; `native_decide`; and every bv_decide proof when the comparator is not
             given `--bv-decide` (which is what check.py does while the support is off)

    python3.12 tests/checker/test_bv_decide.py     # about two minutes (a few dozen Lean starts)

`$SVGOLF_LEAN_WRAP` (a command prefix, e.g. the slot wrapper) applies to every Lean call.
"""

import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
COMPARATOR = os.path.join(SVGOLF, "check", "Comparator.lean")
WRAP = shlex.split(os.environ.get("SVGOLF_LEAN_WRAP", ""))

GOAL = """\
abbrev BvGoal.Goal : Prop := ∀ a b : BitVec 16, (a &&& b) + (a ||| b) = a + b
abbrev BvGoal.Goal2 : Prop :=
  (∀ a b : BitVec 16, (a &&& b) + (a ||| b) = a + b) ∧ (∀ a b : BitVec 16, (a ||| b) - (a &&& b) = a ^^^ b)
abbrev BvGoal.GoalFalse : Prop := 1 = 2
abbrev BvGoal.GoalNat : Prop := (List.range 100).foldl (· + ·) 0 = 4950
"""

HEAD = "import BvGoal\nimport Std.Tactic.BVDecide\nopen Std.Tactic.BVDecide\n"
# ... and importing the real proof (its generated E and C are what the forgeries below re-use)
HEAD2 = HEAD.replace("import BvGoal\n", "import BvGoal\nimport BvSolOk\n", 1)

# the real pair E, C of BvSolOk (the generated names are `<decl>._expr_def_1_1`, `<decl>._cert_def_1_1`)
E = "BvSolOk.solution._expr_def_1_1"
C = "BvSolOk.solution._cert_def_1_1"

SOLS = {
    "BvSolOk": HEAD + "theorem BvSolOk.solution : BvGoal.Goal := by intro a b; bv_decide\n",
    "BvSolTwo": HEAD + """\
theorem BvSolTwo.solution : BvGoal.Goal2 := by
  refine ⟨?_, ?_⟩ <;> intro a b <;> bv_decide
""",
    "BvSolHelper": HEAD + """\
theorem BvSolHelper.helper : ∀ a b : BitVec 16, (a &&& b) + (a ||| b) = a + b := by intro a b; bv_decide
theorem BvSolHelper.solution : BvGoal.Goal := BvSolHelper.helper
""",
    # a hand-written axiom, the generated name, the real pair: a true statement
    "BvSolForgedTrue": HEAD2 + f"""\
axiom BvSolForgedTrue.f._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr {E} {C} = true
theorem BvSolForgedTrue.solution : BvGoal.Goal := by
  have _h := BvSolForgedTrue.f._native.bv_decide.ax_1_1
  exact BvSolOk.solution
""",
    # the attack the old refusal existed for: a satisfiable formula, an empty certificate, and `False`
    "BvSolForgedFalse": HEAD + """\
def BvSolForgedFalse.e : BVLogicalExpr := .const true
def BvSolForgedFalse.c : String := ""
axiom BvSolForgedFalse.solution._native.bv_decide.ax_1_1 :
  Reflect.verifyBVExpr BvSolForgedFalse.e BvSolForgedFalse.c = true
theorem BvSolForgedFalse.solution : BvGoal.GoalFalse := by
  have h := Reflect.unsat_of_verifyBVExpr_eq_true _ _ BvSolForgedFalse.solution._native.bv_decide.ax_1_1
  have h2 : BVLogicalExpr.eval (Lean.RArray.leaf ⟨(0 : BitVec 0)⟩) (.const true) = false := h _
  have h3 : BVLogicalExpr.eval (Lean.RArray.leaf ⟨(0 : BitVec 0)⟩) (BoolExpr.const true) = true := rfl
  rw [h3] at h2
  exact absurd h2 (by decide)
""",
    # a TRUE statement under a name that is not the generated one
    "BvSolOtherName": HEAD2 + f"""\
axiom BvSolOtherName.myax : Reflect.verifyBVExpr {E} {C} = true
theorem BvSolOtherName.solution : BvGoal.Goal := by
  have _h := BvSolOtherName.myax
  exact BvSolOk.solution
""",
    # the generated name over statements of the wrong shape
    "BvSolWrongType": HEAD2 + f"""\
axiom BvSolWrongType.a._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr {E} {C} = false
axiom BvSolWrongType.b._native.bv_decide.ax_1_1 : False
axiom BvSolWrongType.c._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr (BoolExpr.const true) "" = true
axiom BvSolWrongType.d._native.bv_decide.ax_1_1 : ∀ n : Nat, Reflect.verifyBVExpr {E} {C} = true
theorem BvSolWrongType.solution : BvGoal.Goal := by
  have _a := BvSolWrongType.a._native.bv_decide.ax_1_1
  have _b := BvSolWrongType.b._native.bv_decide.ax_1_1
  have _c := BvSolWrongType.c._native.bv_decide.ax_1_1
  have _d := BvSolWrongType.d._native.bv_decide.ax_1_1
  exact BvSolOk.solution
""",
    # TRUE statements that are not in the exact shape: the formula is `id E`, the certificate `C ++ ""`
    "BvSolUnfold": HEAD2 + f"""\
def BvSolUnfold.e : BVLogicalExpr := id {E}
axiom BvSolUnfold.solution._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr BvSolUnfold.e {C} = true
theorem BvSolUnfold.solution : BvGoal.Goal := by
  have _h := BvSolUnfold.solution._native.bv_decide.ax_1_1
  exact BvSolOk.solution
""",
    "BvSolCertNotLit": HEAD2 + f"""\
def BvSolCertNotLit.c : String := {C} ++ ""
axiom BvSolCertNotLit.solution._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr {E} BvSolCertNotLit.c = true
theorem BvSolCertNotLit.solution : BvGoal.Goal := by
  have _h := BvSolCertNotLit.solution._native.bv_decide.ax_1_1
  exact BvSolOk.solution
""",
    # a formula with sharing (2^40 paths in a term of 40 nodes) and one nested 400 deep
    "BvSolDag": HEAD.replace("import Std.Tactic.BVDecide\n", "import Std.Tactic.BVDecide\nimport Lean\n", 1) + """\
open Lean in
run_cmd do
  let c := mkApp2 (mkConst ``BoolExpr.const) (mkConst ``BVPred) (mkConst ``Bool.true)
  let mut x := c
  for _ in [0:40] do
    x := mkApp4 (mkConst ``BoolExpr.gate) (mkConst ``BVPred) (mkConst ``Gate.and) x x
  let mut y := c
  for _ in [0:400] do
    y := mkApp2 (mkConst ``BoolExpr.not) (mkConst ``BVPred) y
  Lean.Elab.Command.liftCoreM <| addDecl <| .defnDecl
    { name := `BvSolDag.e, levelParams := [], type := mkConst ``BVLogicalExpr, value := x,
      hints := .abbrev, safety := .safe }
  Lean.Elab.Command.liftCoreM <| addDecl <| .defnDecl
    { name := `BvSolDag.e2, levelParams := [], type := mkConst ``BVLogicalExpr, value := y,
      hints := .abbrev, safety := .safe }
def BvSolDag.c : String := ""
axiom BvSolDag.solution._native.bv_decide.ax_1_1 : Reflect.verifyBVExpr BvSolDag.e BvSolDag.c = true
axiom BvSolDag.solution._native.bv_decide.ax_1_2 : Reflect.verifyBVExpr BvSolDag.e2 BvSolDag.c = true
theorem BvSolDag.solution : BvGoal.GoalNat := by
  have _h := BvSolDag.solution._native.bv_decide.ax_1_1
  have _h2 := BvSolDag.solution._native.bv_decide.ax_1_2
  decide
""",
    "BvSolReduceBool": HEAD + """\
def BvSolReduceBool.b : Bool := true
theorem BvSolReduceBool.t : BvSolReduceBool.b = true := Lean.ofReduceBool _ _ rfl
theorem BvSolReduceBool.solution : BvGoal.GoalNat := by
  have _h := BvSolReduceBool.t
  decide
""",
    "BvSolNative": HEAD + "theorem BvSolNative.solution : BvGoal.GoalNat := by native_decide\n",
}


def toolchain_lib():
    return subprocess.run(WRAP + ["lean", "--print-libdir"], cwd=SVGOLF, capture_output=True,
                          text=True, check=True).stdout.strip()


class BvDecide(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="svgolf-bvtest-")
        cls.lib = os.path.join(cls.tmp, "lib")
        os.makedirs(cls.lib)
        cls.broken = {}                 # module -> Lean's output, for the modules that did not compile
        cls.compile("BvGoal", GOAL)
        # the real proofs first (the other modules import BvSolOk)
        for m in ("BvSolOk", "BvSolTwo", "BvSolHelper"):
            cls.compile(m, SOLS[m])
        for m, text in SOLS.items():
            if m not in ("BvSolOk", "BvSolTwo", "BvSolHelper"):
                cls.compile(m, text)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @classmethod
    def lean(cls, args):
        env = dict(os.environ, LEAN_PATH=cls.lib)
        return subprocess.run(WRAP + ["lean"] + args, cwd=SVGOLF, env=env, capture_output=True, text=True)

    @classmethod
    def compile(cls, mod, text):
        src = os.path.join(cls.tmp, mod + ".lean")
        with open(src, "w") as fh:
            fh.write(text)
        p = cls.lean(["-R", cls.tmp, "-o", os.path.join(cls.lib, mod + ".olean"), src])
        if p.returncode != 0:
            cls.broken[mod] = p.stdout + p.stderr

    def compare(self, sol, goal="BvGoal.Goal", bv=True, extra=()):
        self.assertNotIn(sol, self.broken, self.broken.get(sol))
        args = ["--run", COMPARATOR, "--goal", goal, "--solution", sol + ".solution", "--module", sol,
                "--prefix", sol, "--allow", "propext,Classical.choice,Quot.sound"]
        if bv:
            args.append("--bv-decide")
        p = self.lean(args + list(extra))
        m = re.search(r"SVGOLF_COMPARATOR (\{.*\})", p.stdout)
        self.assertIsNotNone(m, p.stdout + p.stderr)
        return json.loads(m.group(1))

    def rejected(self, r, *needles):
        self.assertFalse(r["accepted"], r)
        msg = "; ".join(r["errors"])
        for n in needles:
            self.assertIn(n, msg)
        return msg

    # ---- accepted

    def test_a_real_bv_decide_proof_is_accepted_and_reported(self):
        r = self.compare("BvSolOk")
        self.assertTrue(r["accepted"], r["errors"])
        ax = [a for a in r["axioms"] if "bv_decide" in a]
        self.assertEqual(len(ax), 1, r["axioms"])
        self.assertEqual(ax[0].rsplit(".", 3)[1:3], ["_native", "bv_decide"])
        self.assertTrue(r["bv_decide"]["allowed"])
        v = r["bv_decide"]["verified"]
        self.assertEqual([x["axiom"] for x in v], ax)
        self.assertTrue(v[0]["verified"])
        self.assertGreater(v[0]["nodes"], 5)
        self.assertGreater(v[0]["cert_bytes"], 1000)
        # the closure replay is unaffected (the axiom and E, C are the submission's own declarations)
        self.assertTrue(r["replay"]["ok"])

    def test_two_axioms_and_an_axiom_behind_a_helper_lemma_are_each_verified(self):
        r = self.compare("BvSolTwo", goal="BvGoal.Goal2")
        self.assertTrue(r["accepted"], r["errors"])
        self.assertEqual(len(r["bv_decide"]["verified"]), 2, r)
        r = self.compare("BvSolHelper")
        self.assertTrue(r["accepted"], r["errors"])
        self.assertEqual(len(r["bv_decide"]["verified"]), 1, r)

    def test_a_hand_written_axiom_with_the_generated_name_and_a_true_statement_is_accepted(self):
        # indistinguishable from the tactic's own, and a true theorem: accepting it adds nothing to the logic
        r = self.compare("BvSolForgedTrue")
        self.assertTrue(r["accepted"], r["errors"])
        self.assertEqual(len(r["bv_decide"]["verified"]), 2, r)       # its own and the real proof's

    # ---- rejected

    def test_the_forged_axiom_over_a_false_certificate_is_rejected(self):
        r = self.compare("BvSolForgedFalse", goal="BvGoal.GoalFalse")
        # the kernel accepts `theorem _ : 1 = 2 := solution` (the axiom proves False) and the old axiom walk
        # would have seen only an axiom named like bv_decide's: the evaluation is what refuses it
        self.assertTrue(r["kernel_accepts"], r["errors"])
        self.rejected(r, "BvSolForgedFalse.solution._native.bv_decide.ax_1_1", "does not verify",
                      "evaluates to `false`")
        self.assertEqual(r["bv_decide"]["verified"], [])

    def test_the_generated_name_over_the_wrong_shape_is_rejected(self):
        r = self.compare("BvSolWrongType")
        msg = self.rejected(r)
        for n in ("a._native", "b._native", "c._native", "d._native"):
            self.assertIn(f"BvSolWrongType.{n}.bv_decide.ax_1_1 is not accepted", msg)
        self.assertEqual(msg.count("its type is not `verifyBVExpr E C = true`"), 4, msg)

    def test_the_generated_shape_under_another_name_is_an_ordinary_axiom(self):
        r = self.compare("BvSolOtherName")
        msg = self.rejected(r, "axioms outside the allowed set", "BvSolOtherName.myax")
        self.assertNotIn("is not accepted", msg)

    def test_a_true_statement_that_is_not_literally_a_toExpr_value_is_rejected(self):
        r = self.compare("BvSolUnfold")
        self.rejected(r, "BvSolUnfold.e is not a closed `BVLogicalExpr` constructor term")
        r = self.compare("BvSolCertNotLit")
        self.rejected(r, "is not a string literal")

    def test_the_decoding_budget_and_the_depth_limit_stop_a_hostile_term(self):
        r = self.compare("BvSolDag", goal="BvGoal.GoalNat", extra=["--bv-max-nodes", "100000"])
        self.rejected(r, "BvSolDag.solution._native.bv_decide.ax_1_1 is not accepted",
                      "decoding budget exhausted")
        # the 40-node term with 2^40 paths is refused by the node budget, the 400-deep one by the depth limit
        r = self.compare("BvSolDag", goal="BvGoal.GoalNat", extra=["--bv-max-nodes", "100000",
                                                                       "--bv-max-depth", "100"])
        msg = self.rejected(r, "ax_1_2 is not accepted")
        self.assertIn("nested too deeply (--bv-max-depth)", msg)

    def test_ofReduceBool_and_native_decide_stay_rejected(self):
        r = self.compare("BvSolReduceBool", goal="BvGoal.GoalNat")
        self.rejected(r, "axioms outside the allowed set", "Lean.ofReduceBool")
        r = self.compare("BvSolNative", goal="BvGoal.GoalNat")
        self.rejected(r, "axioms outside the allowed set", "_native.native_decide.ax_")

    def test_without_the_flag_every_bv_decide_proof_is_rejected_naming_the_policy(self):
        # what check.py passes while bv_decide is unsupported (decided 2026-11-01): no `--bv-decide`
        r = self.compare("BvSolOk", bv=False)
        msg = self.rejected(r, "`bv_decide` is not supported", "external SAT solver (cadical)",
                            "the checker does not support", "decide +kernel, omega, simp or a symbolic argument")
        self.assertNotIn("allow_bv_decide", msg)       # the policy, not a task switch
        self.assertFalse(r["bv_decide"]["allowed"])
        self.assertEqual(r["bv_decide"]["verified"], [])


if __name__ == "__main__":
    unittest.main(verbosity=1)
