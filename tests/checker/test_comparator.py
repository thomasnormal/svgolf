#!/usr/bin/env python3.12
"""`check/Comparator.lean` on a hand-built module chain (WP-B review round, 2026-10-31), with real
Lean and nothing from Mathlib, the staging tree or the checker's own modules:

    TcGoal   the goal            `abbrev Goal : Prop := 1 = 2` (false) and `Goal2 : Prop := 1 + 1 = 2`
    TcPkg    a "package"         an honest lemma, in its own directory on the search path
    TcEvil   a planted "package" `theorem evil : False := True.intro`, added to the environment WITH
                                 THE KERNEL CHECK SWITCHED OFF (`debug.skipKernelTC`); no axiom
                                 anywhere in its value
    TcAx     a package axiom     `axiom ax : False`
    TcSol*   the "solutions"     each `import`s one of them

What each case pins (the comparator is run exactly as `check.py` runs it):

  * the honest chain is accepted; the report carries the direct imports of the solution module,
    the number of toolchain modules it checked and the replay (closure, replayed, ok);
  * `TcEvil`: the comparator's kernel check of `theorem _ : Goal := solution` and its axiom walk both
    PASS (`kernel_accepts` true, no axiom: that is the hole the review found), and the comparator
    still REJECTS, with the kernel's own error from the replay of the dependency closure, naming
    `TcEvil.evil`;
  * `TcAx`: an axiom in a package is rejected by the axiom walk (unchanged);
  * a module of the Lean toolchain (a byte-identical copy of `Lake/Util/Casing.olean`, which
    Mathlib reaches) that resolves to a directory AHEAD of the toolchain's is rejected: Lean resolves
    a module root to the first search-path entry with a directory of that name, so a package
    build directory could otherwise stand in for the toolchain, which the replay takes as given;
  * the submission's own constants are not replayed (`leanchecker`'s job): an `extern` in a
    module under `--prefix` is still found, through the module data and not a walk over every
    constant.

    python3.12 tests/checker/test_comparator.py     # about a minute (a dozen Lean starts)

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
abbrev TcGoal.Goal : Prop := 1 = 2
abbrev TcGoal.Goal2 : Prop := 1 + 1 = 2
abbrev TcGoal.GoalLat (lat : Nat → Nat) : Prop := lat 3 = 5 ∧ ∀ n, 1 ≤ lat n
"""
# a tx-family goal applied to the solution's latency (`--goal-arg`, Comparator point 7)
LAT = """\
import TcGoal
def TcSolLat.lat (n : Nat) : Nat := n + 2
def TcSolLat.lat3 (n : Nat) : Nat := n + 3
opaque TcSolLat.op : Nat → Nat
theorem TcSolLat.solution : TcGoal.GoalLat TcSolLat.lat := ⟨rfl, fun n => by unfold TcSolLat.lat; omega⟩
"""
PKG = """\
theorem TcPkg.honest : 1 + 1 = 2 := rfl
"""
EVIL = """\
import Lean
open Lean Elab Command

/-! A package module whose theorem was added WITHOUT kernel checking. -/
set_option debug.skipKernelTC true in
run_cmd do
  liftCoreM <| addDecl <| .thmDecl
    { name := `TcEvil.evil, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }
"""
AX = "axiom TcAx.ax : False\n"
EXTERN = """\
import TcGoal
@[extern "lean_nat_add"] def TcSolExtern.fastAdd (a b : Nat) : Nat := a + b
theorem TcSolExtern.solution : TcGoal.Goal2 := rfl
"""
# (module, text): the solutions
SOLS = {
    "TcSolOk": "import TcGoal\nimport TcPkg\ntheorem TcSolOk.solution : TcGoal.Goal2 := TcPkg.honest\n",
    "TcSolEvil": "import TcGoal\nimport TcEvil\ntheorem TcSolEvil.solution : TcGoal.Goal := TcEvil.evil.elim\n",
    "TcSolAx": "import TcGoal\nimport TcAx\ntheorem TcSolAx.solution : TcGoal.Goal := TcAx.ax.elim\n",
    "TcSolShadow": "import TcGoal\nimport Lake.Util.Casing\ntheorem TcSolShadow.solution : TcGoal.Goal2 := rfl\n",
    "TcSolExtern": EXTERN,
    "TcSolLat": LAT,
}


def toolchain_lib():
    out = subprocess.run(WRAP + ["lean", "--print-libdir"], cwd=SVGOLF, capture_output=True,
                         text=True, check=True).stdout.strip()
    return out


class Comparator(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="svgolf-cmptest-")
        cls.lib = os.path.join(cls.tmp, "lib")
        cls.pkg = os.path.join(cls.tmp, "pkg")           # where the "packages" live
        cls.shadow = os.path.join(cls.tmp, "shadow")     # a directory AHEAD of the toolchain
        for d in (cls.lib, cls.pkg, cls.shadow):
            os.makedirs(d)
        cls.compile("TcGoal", GOAL, cls.lib)
        cls.compile("TcPkg", PKG, cls.pkg)
        cls.compile("TcEvil", EVIL, cls.pkg)
        cls.compile("TcAx", AX, cls.pkg)
        for m, text in SOLS.items():
            cls.compile(m, text, cls.lib)
        # a byte-identical copy of a toolchain module, in a directory ahead of the toolchain's
        src = os.path.join(toolchain_lib(), "Lake", "Util")
        os.makedirs(os.path.join(cls.shadow, "Lake", "Util"))
        copied = 0
        for n in os.listdir(src):
            if n.startswith("Casing.olean"):
                shutil.copy(os.path.join(src, n), os.path.join(cls.shadow, "Lake", "Util", n))
                copied += 1
        assert copied, "Lake/Util/Casing.olean* not found in the toolchain"

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    @classmethod
    def lean(cls, args, path):
        env = dict(os.environ, LEAN_PATH=":".join(path))
        return subprocess.run(WRAP + ["lean"] + args, cwd=SVGOLF, env=env, capture_output=True,
                              text=True)

    @classmethod
    def compile(cls, mod, text, outdir, path=None):
        src = os.path.join(cls.tmp, mod + ".lean")
        with open(src, "w") as fh:
            fh.write(text)
        p = cls.lean(["-R", cls.tmp, "-o", os.path.join(outdir, mod + ".olean"), src],
                     [cls.lib, cls.pkg] if path is None else path)
        assert p.returncode == 0, (mod, p.stdout + p.stderr)

    def compare(self, sol, goal="TcGoal.Goal2", path=None, allow="propext,Classical.choice,Quot.sound",
                extra=()):
        p = self.lean(["--run", COMPARATOR, "--goal", goal, "--solution", sol + ".solution",
                       "--module", sol, "--prefix", sol, "--allow", allow, *extra],
                      [self.lib, self.pkg] if path is None else path)
        m = re.search(r"SVGOLF_COMPARATOR (\{.*\})", p.stdout)
        self.assertIsNotNone(m, p.stdout + p.stderr)
        return json.loads(m.group(1))

    def test_the_honest_chain_is_accepted_and_reported(self):
        r = self.compare("TcSolOk")
        self.assertTrue(r["accepted"], r["errors"])
        # `Init` is implicit (and listed twice: once with each import flag)
        self.assertEqual(sorted(set(r["imports"]["TcSolOk"])), ["Init", "TcGoal", "TcPkg"])
        self.assertGreater(r["toolchain_modules"], 100)
        self.assertTrue(r["replay"]["ok"])
        self.assertGreaterEqual(r["replay"]["replayed"], 1)         # TcPkg.honest, at least
        self.assertGreaterEqual(r["replay"]["closure"], r["replay"]["replayed"])

    def test_a_declaration_added_without_the_kernel_is_caught_by_the_replay(self):
        r = self.compare("TcSolEvil", goal="TcGoal.Goal")
        # the two checks the comparator had before: both pass, which is the hole
        self.assertTrue(r["kernel_accepts"], r["errors"])
        self.assertEqual(r["axioms"], [])
        # the replay is what catches it
        self.assertFalse(r["accepted"])
        self.assertFalse(r["replay"]["ok"])
        msg = "; ".join(r["errors"])
        self.assertIn("kernel replay of the dependency closure failed", msg)
        self.assertIn("TcEvil.evil", msg)
        self.assertIn("declaration type mismatch", msg)

    def test_a_package_axiom_is_still_rejected_by_the_axiom_walk(self):
        r = self.compare("TcSolAx", goal="TcGoal.Goal")
        self.assertFalse(r["accepted"])
        self.assertEqual(r["axioms"], ["TcAx.ax"])
        self.assertIn("axioms outside the allowed set", "; ".join(r["errors"]))

    def test_a_toolchain_module_ahead_of_the_toolchain_is_rejected(self):
        r = self.compare("TcSolShadow", path=[self.shadow, self.lib, self.pkg])
        self.assertFalse(r["accepted"])
        msg = "; ".join(r["errors"])
        self.assertIn("resolve outside", msg)
        self.assertIn("Lake.Util.Casing", msg)
        self.assertIn(self.shadow, msg)
        # the same module from the toolchain itself is fine
        r = self.compare("TcSolShadow")
        self.assertTrue(r["accepted"], r["errors"])

    def test_an_extern_in_a_submission_module_is_found_through_the_module_data(self):
        r = self.compare("TcSolExtern")
        self.assertFalse(r["accepted"])
        self.assertIn("`extern`/`implemented_by` on submission constants", "; ".join(r["errors"]))
        self.assertIn("TcSolExtern.fastAdd", "; ".join(r["errors"]))

    def test_a_goal_applied_to_the_solutions_latency(self):
        def cmp(arg):
            return self.compare("TcSolLat", goal="TcGoal.GoalLat", extra=["--goal-arg", arg])
        r = cmp("TcSolLat.lat")
        self.assertTrue(r["accepted"], r["errors"])
        self.assertTrue(r["syntactic_match"])
        self.assertEqual(r["goal_arg"], "TcSolLat.lat")
        # another latency than the one proved: the kernel rejects the application
        r = cmp("TcSolLat.lat3")
        self.assertFalse(r["accepted"])
        self.assertIn("the kernel rejects", "; ".join(r["errors"]))
        # not a definition, or absent
        self.assertIn("must be a definition", "; ".join(cmp("TcSolLat.op")["errors"]))
        self.assertIn("no constant TcSolLat.nope", "; ".join(cmp("TcSolLat.nope")["errors"]))
        # without `--goal-arg`, a function-valued goal is not a statement
        self.assertFalse(self.compare("TcSolLat", goal="TcGoal.GoalLat")["accepted"])


if __name__ == "__main__":
    unittest.main(verbosity=1)
