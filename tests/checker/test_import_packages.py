#!/usr/bin/env python3.12
"""Imports from the Mathlib packages (WP-B, 2026-10-31, and its review round), without Lean:
`check.py`'s real source / extract / banlist / fourstate stages run on the `_example` reference
design (pyslang, the extractor and Yosys), and the Lean runner is a fake whose `compile` answers
what Lean would for the generated `Submission.ImportProbe` (the solution's package imports,
compiled alone), whose `run` answers `lake env printenv LEAN_PATH` with a search path made of
temporary directories and the comparator with a report, and whose compile of `Solution.lean` can
DO something (the solution's own build is arbitrary code):

class Packages (the early stages and the import probe)
  * a solution importing `Mathlib.Tactic.Ring` passes the `imports` stage, the probe carries
    exactly that import and is compiled once, before the design; `stages.packages` records the
    revisions of the checkouts;
  * a lookalike (`Mathlib2.Tactic`) is rejected at `imports`, with no probe; a comment between two
    imports on one line does not hide the second (a glued `LeanModels.Python.*` import is rejected,
    a glued Mathlib import is probed);
  * the probe failing because the package's build products are ABSENT (`unknown module prefix`),
    because a module only a TRANSITIVE import needs is missing (the `Mathlib` umbrella on a
    machine without all of Batteries), or because a module the player named has a source in the
    packages but no olean on this machine (`import Batteries`), is an INFRASTRUCTURE error
    (RuntimeError, exit 2), never a Reject: the verdict must not depend on the machine; any other
    probe failure (an incompatible olean, a crash with no output) is one too, and says the exit
    status and the package directories;
  * a module the player named that no package has a source for (a stale `Mathlib.Data.Nat.Defs`)
    is a REJECTION at `imports` naming it;
  * a package on no entry of the search path, or a checkout not at the revision the manifest pins,
    is an infrastructure error;
  * a solution without a package import costs no probe, and its tripwire still watches the
    search path.

class Tripwire (the REAL `integrity_snapshot` inside `check`, the solution's build doing
something)
  * nothing changed: the run reaches the comparator;
  * a package-free solution whose build changes, adds or deletes a `.olean`, `.olean.server` or
    `.olean.private` of a package on the search path, creates a search-path entry that did not
    exist (`Cli`'s build directory, ahead of Mathlib's), creates a module root in an entry (a
    shadow `Mathlib/`), or edits lean-surfaces' `lake-manifest.json`, is rejected at `integrity`;
  * `.ilean`/`.hash`/`.trace` noise is not seen;
  * the comparator's report of the imports Lean recorded is checked against the header the
    checker read (`import_mismatch`): a hidden or an unlisted import is rejected at `imports`.

class BvDecideFlag (WP-BV, the same fake Lean)
  * bv_decide is NOT SUPPORTED (decided 2026-11-01): `check.py`'s `BV_DECIDE_SUPPORTED` is a constant, False, that no
    environment variable, option or task key can change (an AST test pins it); `allow_bv_decide` absent or false
    forbids it, `true` and non-booleans are infrastructure errors; the solution's compile gets `bv_solver=False` and
    the comparator no `--bv-decide`; with the constant forced True inside a test the old behaviour (allowed by
    default) is back;
  * a failed compile of a solution that uses `bv_decide` carries a HINT at the `solution` stage when the message is
    the sandbox's opaque `operation not permitted` at a `bv_decide` line, or names the solver; not for a file that
    only mentions it in a comment or has an unrelated error.

The real Lean side (a Mathlib-tactic proof accepted; `native_decide` behind it rejected at the
comparator; an unchanged tactic reference with `Mathlib.Tactic.Ring`; the kernel replay of a
planted `False`) is `tests/run.py`'s `attacks` and `comparator` steps.

    python3.12 tests/checker/test_import_packages.py
"""

import importlib.util
import json
import os
import re
import shutil
import sys
import tempfile
import time
import unittest
from unittest import mock

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


checkpy = load("svgolf_check_py_packages", os.path.join(SVGOLF, "check.py"))
TASK = os.path.join(SVGOLF, "tasks", "_example")
SV = os.path.join(TASK, "reference", "band.sv")
_REAL_SOURCE_EXISTS = checkpy.package_source_exists     # `Base.setUp` stubs the module's name


class FakeLean:
    """Stands in for check.py's `Lean`: `compile` of the import probe answers `probe_answer`,
    `run` of `printenv LEAN_PATH` answers `search_path`, the comparator answers `comparator`
    (None: nothing), every other compile and run answer as a run that got past its stage;
    `on_solution`, if set, runs when `Solution.lean` is compiled (the solution's own build)."""
    probe_answer = (0, "", 1.5)
    compiled = []          # (basename, text) in order
    search_path = []
    comparator = None
    on_solution = None
    solution_answer = None  # (rc, output, seconds) for the compile of Solution.lean (WP-BV: a refused bv_decide)
    run_args = []          # every `run` call, in order (WP-BV: the comparator's command line)
    compile_kw = {}        # basename -> the keyword arguments of its `compile` (WP-BV: `bv_solver`)

    def __init__(self, stage, wrap):
        self.stage, self.wrap = stage, wrap
        self.build = os.path.join(stage, "build")

    def run(self, args, timeout=None, lake_env=True, **kw):
        FakeLean.run_args.append(list(args))
        if args[:2] == ["printenv", "LEAN_PATH"]:
            return 0, ":".join(FakeLean.search_path) + "\n", 0.1
        if args[:2] == ["lean", "--run"] and FakeLean.comparator is not None:
            return 0, "SVGOLF_COMPARATOR " + json.dumps(FakeLean.comparator) + "\n", 0.1
        return 0, "", 0.1

    def compile(self, module_path, timeout=None, **kw):
        base = os.path.basename(module_path)
        FakeLean.compile_kw[base] = kw
        with open(module_path) as fh:
            FakeLean.compiled.append((base, fh.read()))
        if base == "ImportProbe.lean":
            return FakeLean.probe_answer
        if base == "Solution.lean" and FakeLean.on_solution:
            FakeLean.on_solution()
        if base == "Solution.lean" and FakeLean.solution_answer is not None:
            return FakeLean.solution_answer
        return 0, "SVGOLF_UNSUPPORTED_FREE 4\n", 0.1


def solution_text(tmp, text):
    path = os.path.join(tmp, "Solution.lean")
    with open(path, "w") as fh:
        fh.write(text)
    return path


def solution(tmp, *imports):
    return solution_text(tmp, "import Submission.Design\n" + "".join(f"import {m}\n" for m in imports)
                         + "namespace Submission\ntheorem solution : Goal := trivial\nend Submission\n")


REVS = {"mathlib": {"manifest": "a" * 40, "checkout": "a" * 40},
        "batteries": {"manifest": "b" * 40, "checkout": "b" * 40}}


class Base(unittest.TestCase):
    """A temporary Lean search path: an entry that does not exist (like `Cli`'s build directory),
    Mathlib's build directory with a few oleans, and Batteries'."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="svgolf-pkgtest-")
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        self.lib = os.path.join(self.tmp, "pk", "mathlib", ".lake", "build", "lib", "lean")
        self.bat = os.path.join(self.tmp, "pk", "batteries", ".lake", "build", "lib", "lean")
        self.absent = os.path.join(self.tmp, "pk", "Cli", ".lake", "build", "lib", "lean")
        os.makedirs(os.path.join(self.lib, "Mathlib", "Tactic"))
        os.makedirs(os.path.join(self.bat, "Batteries"))
        for f in ("Mathlib.olean", os.path.join("Mathlib", "Tactic", "Ring.olean")):
            open(os.path.join(self.lib, f), "w").close()
        open(os.path.join(self.bat, "Batteries", "Basic.olean"), "w").close()
        FakeLean.probe_answer, FakeLean.compiled = (0, "", 1.5), []
        FakeLean.run_args, FakeLean.compile_kw, FakeLean.solution_answer = [], {}, None
        FakeLean.search_path = [self.absent, self.lib, self.bat]
        FakeLean.comparator = FakeLean.on_solution = None
        self.snap_args = []
        self._saved = {n: getattr(checkpy, n) for n in
                       ("Lean", "integrity_snapshot", "package_revisions", "package_source_exists",
                        "LS_ROOT", "LAYOUT", "SVGOLF", "_tool_trees")}
        self._saved_trusted = checkpy.postsynth.trusted_files
        # the fake trees below are of the layout inside lean-surfaces (`ls/` holds the packages and
        # the manifest), whichever layout this test runs in (check/layout.py)
        checkpy.LAYOUT = "inside"
        checkpy.Lean = FakeLean
        checkpy.package_revisions = lambda: REVS
        checkpy.package_source_exists = lambda m: False
        self.addCleanup(self._restore)

    def _restore(self):
        for n, v in self._saved.items():
            setattr(checkpy, n, v)
        checkpy.postsynth.trusted_files = self._saved_trusted

    def check(self, *imports):
        return self.run_check(solution(self.tmp, *imports))

    def run_check(self, sol):
        stage = os.path.join(self.tmp, "stage")
        shutil.rmtree(stage, ignore_errors=True)
        os.makedirs(stage)
        return checkpy.check(TASK, SV, sol, stage, [], do_score=False, build_trusted=False)

    def probes(self):
        return [t for n, t in FakeLean.compiled if n == "ImportProbe.lean"]


class BvDecideFlag(Base):
    """WP-BV, as ruled on 2026-11-01 ("Let's not support external solvers for now"): bv_decide is NOT
    SUPPORTED. `check.py`'s `BV_DECIDE_SUPPORTED` is False, so `allow_bv_decide` absent or false forbids it,
    `true` is an infrastructure error, the solution's compile never gets the solver and the comparator is never
    given `--bv-decide`; a refused bv_decide proof carries a hint. With the constant forced True (the dormant
    groundwork, here only inside a test) the old behaviour is back: allowed by default, `false` forbids it."""

    def setUp(self):
        super().setUp()
        checkpy.integrity_snapshot = lambda stage, search_path=(): {}
        self.addCleanup(setattr, checkpy, "BV_DECIDE_SUPPORTED", checkpy.BV_DECIDE_SUPPORTED)

    def task_dir(self, **keys):
        d = os.path.join(self.tmp, "task")
        shutil.rmtree(d, ignore_errors=True)
        shutil.copytree(TASK, d)
        with open(os.path.join(d, "task.json")) as fh:
            t = json.load(fh)
        t.pop("allow_bv_decide", None)
        t.update(keys)
        with open(os.path.join(d, "task.json"), "w") as fh:
            json.dump(t, fh)
        return d

    def go(self, task_dir, sol=None):
        stage = os.path.join(self.tmp, "stage")
        shutil.rmtree(stage, ignore_errors=True)
        os.makedirs(stage)
        FakeLean.run_args, FakeLean.compile_kw = [], {}
        res = checkpy.check(task_dir, SV, sol or solution(self.tmp), stage, [], do_score=False, build_trusted=False)
        comp = [a for a in FakeLean.run_args if a[:2] == ["lean", "--run"]]
        return res, comp

    def test_the_shipped_tasks_do_not_enable_it(self):
        for name in ("_example", "add", "mul", "aes_sbox", "clmul", "fdivp"):
            with open(os.path.join(SVGOLF, "tasks", name, "task.json")) as fh:
                self.assertIs(json.load(fh).get("allow_bv_decide", False), False, name)

    def test_the_support_is_a_constant_of_check_py_and_nothing_reads_it_from_outside(self):
        import ast
        with open(os.path.join(SVGOLF, "check.py")) as fh:
            tree = ast.parse(fh.read())
        self.assertIs(checkpy.BV_DECIDE_SUPPORTED, False)
        assigns = [n for n in ast.walk(tree) if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign))
                   and any(isinstance(t, ast.Name) and t.id == "BV_DECIDE_SUPPORTED"
                           for t in (n.targets if isinstance(n, ast.Assign) else [n.target]))]
        self.assertEqual(len(assigns), 1)                                       # one definition, never rebound
        self.assertIsInstance(assigns[0].value, ast.Constant)
        self.assertIs(assigns[0].value.value, False)
        self.assertEqual([n for n in ast.walk(tree) if isinstance(n, ast.Global)
                          and "BV_DECIDE_SUPPORTED" in n.names], [])
        # no environment variable, and no command-line option, mentions it
        names = [n.value for n in ast.walk(tree) if isinstance(n, ast.Constant) and isinstance(n.value, str)]
        env_reads = [n for n in ast.walk(tree) if isinstance(n, ast.Attribute) and n.attr in ("environ", "getenv")]
        self.assertTrue(env_reads)
        for n in ast.walk(tree):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == "add_argument":
                for a in n.args:
                    self.assertNotIn("bv", getattr(a, "value", "").lower(), "no option may enable bv_decide")
        for n in ast.walk(tree):
            if isinstance(n, (ast.Subscript, ast.Call)):
                src = ast.unparse(n)
                if "environ" in src or "getenv" in src:
                    self.assertNotIn("BV_DECIDE", src)
                    self.assertNotIn("bv_decide", src.lower())
        self.assertTrue(names)

    def test_absent_or_false_forbids_it_and_nothing_is_granted(self):
        for keys in ({}, {"allow_bv_decide": False}):
            res, comp = self.go(self.task_dir(**keys))
            self.assertEqual(res["stage"], "comparator", res["errors"])          # past the solution stage
            self.assertEqual(FakeLean.compile_kw["Solution.lean"], {"bv_solver": False, "progress": True, "cpu_limit": 300})
            self.assertEqual(FakeLean.compile_kw["Design.lean"], {})
            (cargs,) = comp
            self.assertNotIn("--bv-decide", cargs)

    def test_true_is_an_infrastructure_error_not_a_verdict(self):
        with self.assertRaises(RuntimeError) as cm:
            self.go(self.task_dir(allow_bv_decide=True))
        self.assertIn("does not support external SAT solvers", str(cm.exception))
        self.assertIn("allow_bv_decide must be false or absent", str(cm.exception))
        self.assertEqual(FakeLean.compile_kw, {})                                  # before any compile

    def test_anything_but_a_boolean_is_an_error_too(self):
        for bad in ("yes", 1, None, "false"):
            with self.assertRaises(RuntimeError) as cm:
                self.go(self.task_dir(allow_bv_decide=bad))
            self.assertIn("allow_bv_decide must be false or absent", str(cm.exception))

    def test_with_the_dormant_support_forced_on_it_is_allowed_by_default_and_false_forbids_it(self):
        checkpy.BV_DECIDE_SUPPORTED = True                                         # inside this test only
        for keys in ({}, {"allow_bv_decide": True}):
            res, comp = self.go(self.task_dir(**keys))
            self.assertEqual(res["stage"], "comparator", res["errors"])
            self.assertEqual(FakeLean.compile_kw["Solution.lean"], {"bv_solver": True, "progress": True, "cpu_limit": 300})
            self.assertEqual(FakeLean.compile_kw["Design.lean"], {})              # no other compile gets the solver
            self.assertIn("--bv-decide", comp[0])
        res, comp = self.go(self.task_dir(allow_bv_decide=False))
        self.assertEqual(FakeLean.compile_kw["Solution.lean"], {"bv_solver": False, "progress": True, "cpu_limit": 300})
        self.assertNotIn("--bv-decide", comp[0])

    # ---- the hint at the `solution` stage (sandbox on: the solver cannot start, the message is opaque)

    BV_SOL = ("import Submission.Design\nimport Std.Tactic.BVDecide\nnamespace Submission\n"
              "theorem helper : \u2200 a b : BitVec 16, (a &&& b) + (a ||| b) = a + b := by\n"
              "  intro a b\n  bv_decide\ntheorem solution : Goal := trivial\nend Submission\n")

    def refused(self, text, answer):
        FakeLean.solution_answer = answer
        return self.go(self.task_dir(), solution_text(self.tmp, text))[0]

    def test_a_bv_decide_the_sandbox_refused_carries_the_hint(self):
        # the sandbox's message names neither the tactic nor the solver: `operation not permitted`, at the line of `bv_decide`
        res = self.refused(self.BV_SOL, (1, "/stage/Submission/Solution.lean:6:2: error: operation not permitted "
                                          "(error code: 4294967295)\n", 1.0))
        self.assertEqual((res["accepted"], res["stage"]), (False, "solution"))
        msg = "\n".join(res["errors"])
        self.assertIn("the proof does not compile", msg)
        self.assertIn("HINT: bv_decide runs an external SAT solver (cadical), which the checker does not support", msg)
        self.assertIn("decide +kernel, omega, simp or a symbolic argument", msg)

    def test_the_hint_finds_the_line_through_a_multi_line_comment(self):
        # Lean's positions count the lines of the file as written: a block comment above must not shift them
        text = self.BV_SOL.replace("namespace Submission\n", "/-! A long\ncomment over\nthree lines. -/\nnamespace Submission\n", 1)
        line = [i for i, ln in enumerate(text.splitlines(), 1) if ln.strip() == "bv_decide"][0]
        res = self.refused(text, (1, f"/s/Submission/Solution.lean:{line}:2: error: operation not permitted\n", 1.0))
        self.assertIn("HINT: bv_decide runs an external SAT solver", "\n".join(res["errors"]))
        res = self.refused(text, (1, f"/s/Submission/Solution.lean:{line - 4}:2: error: operation not permitted\n", 1.0))
        self.assertNotIn("HINT", "\n".join(res["errors"]))             # a line that does not mention it

    def test_a_missing_solver_or_one_that_could_not_start_carries_the_hint_too(self):
        for out in ("/s/Submission/Solution.lean:3:0: error: Failed to execute external prover:\n"
                    "could not execute external process '/tc/bin/cadical'\n",
                    "/s/Submission/Solution.lean:6:2: error: The SAT solver timed out while solving the problem.\n"):
            res = self.refused(self.BV_SOL, (1, out, 1.0))
            self.assertIn("HINT: bv_decide runs an external SAT solver", "\n".join(res["errors"]), out)

    def test_no_hint_when_the_failure_is_not_about_bv_decide(self):
        plain = self.BV_SOL.replace("bv_decide", "omega")
        # the same opaque message at the same line, but no bv_decide in the file
        res = self.refused(plain, (1, "/s/Submission/Solution.lean:6:2: error: operation not permitted\n", 1.0))
        self.assertNotIn("HINT", "\n".join(res["errors"]))
        # bv_decide only in a comment
        res = self.refused(self.BV_SOL.replace("  bv_decide\n", "  omega\n-- bv_decide would be shorter\n"),
                           (1, "/s/Submission/Solution.lean:6:2: error: operation not permitted\n", 1.0))
        self.assertNotIn("HINT", "\n".join(res["errors"]))
        # bv_decide in the file, but the error is somewhere else and does not name the solver
        res = self.refused(self.BV_SOL, (1, "/s/Submission/Solution.lean:8:0: error: unknown identifier 'x'\n", 1.0))
        self.assertNotIn("HINT", "\n".join(res["errors"]))

    def test_no_hint_when_the_dormant_support_is_on(self):
        checkpy.BV_DECIDE_SUPPORTED = True
        res = self.refused(self.BV_SOL, (1, "/s/Submission/Solution.lean:6:2: error: operation not permitted\n", 1.0))
        self.assertNotIn("HINT", "\n".join(res["errors"]))


class Packages(Base):
    def setUp(self):
        super().setUp()
        checkpy.integrity_snapshot = lambda stage, search_path=(): (
            self.snap_args.append(list(search_path)) or {})

    def test_a_mathlib_import_passes_the_imports_stage(self):
        res = self.check("Mathlib.Tactic.Ring", "Mathlib.Tactic.Linarith", "LeanModels.Sv.CombLib")
        # past `imports`: the fake comparator prints nothing, which is its own rejection
        self.assertEqual(res["stage"], "comparator", res["errors"])
        self.assertEqual(res["stages"]["imports"]["rejected"], [])
        self.assertEqual(res["stages"]["packages"],
                         {"imports": ["Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring"],
                          "exit": 0, "seconds": 1.5, "revisions": REVS})
        (text,) = self.probes()
        self.assertEqual([ln for ln in text.splitlines() if ln.startswith("import")],
                         ["import Mathlib.Tactic.Linarith", "import Mathlib.Tactic.Ring"])
        # Lean: `import` must precede every command, a `/-! -/` doc comment included (the first
        # real run of the probe failed on exactly that); only `--` comments may come before
        first = next(ln for ln in text.splitlines() if not ln.startswith("--"))
        self.assertTrue(first.startswith("import "), text)
        self.assertNotIn("/-", text)
        self.assertEqual([n for n, _ in FakeLean.compiled][:2],
                         ["ImportProbe.lean", "Design.lean"])           # the probe comes first
        self.assertEqual(self.snap_args, [FakeLean.search_path] * 2)    # the tripwire watches it

    def test_a_lookalike_is_rejected_at_imports_without_a_probe(self):
        res = self.check("Mathlib2.Tactic")
        self.assertEqual((res["accepted"], res["stage"]), (False, "imports"))
        self.assertIn("Mathlib2.Tactic", res["errors"][0])
        self.assertEqual(self.probes(), [])

    def test_an_ordinary_solution_costs_no_probe_but_the_tripwire_watches_the_search_path(self):
        res = self.check("LeanModels.Sv.CombLib")
        self.assertEqual(res["stage"], "comparator", res["errors"])
        self.assertEqual(self.probes(), [])
        self.assertNotIn("packages", res["stages"])
        # WP-B review: a package-free solution can plant an olean a later run would load
        self.assertEqual(self.snap_args, [FakeLean.search_path] * 2)

    def test_a_comment_between_two_imports_does_not_hide_the_second(self):
        res = self.run_check(solution_text(
            self.tmp, "import Submission.Design\nimport SvGolf.Comb/-c-/import LeanModels.Python.Semantics\n"
            "namespace Submission\ntheorem solution : Goal := trivial\nend Submission\n"))
        self.assertEqual((res["accepted"], res["stage"]), (False, "imports"))
        self.assertIn("LeanModels.Python.Semantics", res["errors"][0])
        res = self.run_check(solution_text(
            self.tmp, "import Submission.Design\nimport SvGolf.Comb/-c-/import Mathlib.Tactic.Ring\n"
            "namespace Submission\ntheorem solution : Goal := trivial\nend Submission\n"))
        self.assertEqual(res["stages"]["imports"]["imports"],
                         ["Submission.Design", "SvGolf.Comb", "Mathlib.Tactic.Ring"])
        self.assertEqual(res["stages"]["packages"]["imports"], ["Mathlib.Tactic.Ring"])
        self.assertEqual(len(self.probes()), 1)

    def test_missing_package_products_are_an_infrastructure_error(self):
        FakeLean.probe_answer = (1, "Submission/ImportProbe.lean:1:0: error: unknown module "
                                 "prefix 'Mathlib'\n\nNo directory 'Mathlib' or file "
                                 "'Mathlib.olean' in the search path entries:\n/x/lib\n", 0.3)
        with self.assertRaises(RuntimeError) as cm:
            self.check("Mathlib.Tactic.Ring")
        self.assertIn("infrastructure", str(cm.exception))
        self.assertIn("unknown module prefix 'Mathlib'", str(cm.exception))

    def test_a_package_on_no_search_path_entry_is_an_infrastructure_error(self):
        FakeLean.search_path = [self.absent, self.bat]          # no Mathlib directory anywhere
        with self.assertRaises(RuntimeError) as cm:
            self.check("Mathlib.Tactic.Ring")
        self.assertIn("infrastructure", str(cm.exception))
        self.assertIn("Mathlib", str(cm.exception))
        self.assertEqual(self.probes(), [])     # not probed: the answer is known without Lean

    def test_a_checkout_at_another_revision_is_an_infrastructure_error(self):
        checkpy.package_revisions = lambda: {
            "mathlib": {"manifest": "a" * 40, "checkout": "c" * 40}}
        with self.assertRaises(RuntimeError) as cm:
            self.check("Mathlib.Tactic.Ring")
        self.assertIn("lake-manifest.json", str(cm.exception))
        self.assertIn("mathlib", str(cm.exception))
        # a checkout whose revision cannot be read is not a mismatch
        checkpy.package_revisions = lambda: {"mathlib": {"manifest": "a" * 40, "checkout": None}}
        self.assertEqual(self.check("Mathlib.Tactic.Ring")["stage"], "comparator")

    def test_a_missing_transitive_module_is_an_infrastructure_error(self):
        FakeLean.probe_answer = (1, "Submission/ImportProbe.lean:1:0: error: object file "
                                 "'/p/batteries/.lake/build/lib/lean/Batteries.olean' of module "
                                 "Batteries does not exist\n", 0.3)
        with self.assertRaises(RuntimeError) as cm:
            self.check("Mathlib")          # the umbrella: Batteries is not a direct import
        self.assertIn("infrastructure", str(cm.exception))

    def test_a_named_module_with_a_source_but_no_olean_is_an_infrastructure_error(self):
        # `import Batteries`: the package has Batteries.lean, this machine did not build it
        FakeLean.probe_answer = (1, "Submission/ImportProbe.lean:1:0: error: object file "
                                 "'/p/batteries/.lake/build/lib/lean/Batteries.olean' of module "
                                 "Batteries does not exist\n", 0.3)
        checkpy.package_source_exists = lambda m: m == "Batteries"
        with self.assertRaises(RuntimeError) as cm:
            self.check("Batteries")
        self.assertIn("infrastructure", str(cm.exception))
        self.assertIn("not built on this machine", str(cm.exception))

    def test_any_other_probe_failure_is_an_infrastructure_error(self):
        FakeLean.probe_answer = (1, "error: failed to read file 'x.olean', incompatible header\n",
                                 0.3)
        with self.assertRaises(RuntimeError):
            self.check("Mathlib.Tactic.Ring")

    def test_a_probe_that_dies_silently_is_an_infrastructure_error_that_says_how(self):
        FakeLean.probe_answer = (-11, "", 0.3)           # a truncated olean: SIGSEGV, no output
        with self.assertRaises(RuntimeError) as cm:
            self.check("Mathlib.Tactic.Ring")
        msg = str(cm.exception)
        self.assertIn("exited -11", msg)
        self.assertIn("signal 11", msg)
        self.assertIn("printed nothing", msg)
        # the package build directories of the search path are named, the toolchain's are not:
        # the operator knows where to look
        res = checkpy.classify_import_probe(["Mathlib.Tactic.Ring"], 1, "", search_path=[
            "/p/.lake/packages/mathlib/.lake/build/lib/lean", "/tc/lib/lean"])
        self.assertEqual(res[0], "infra")
        self.assertIn("/p/.lake/packages/mathlib/.lake/build/lib/lean", res[1])
        self.assertNotIn("/tc/lib/lean", res[1])

    def test_a_nonexistent_module_the_player_named_is_a_rejection(self):
        FakeLean.probe_answer = (1, "Submission/ImportProbe.lean:1:0: error: object file "
                                 "'/p/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/Defs.olean' "
                                 "of module Mathlib.Data.Nat.Defs does not exist\n", 0.3)
        res = self.check("Mathlib.Data.Nat.Defs")           # no package has a source for it
        self.assertEqual((res["accepted"], res["stage"]), (False, "imports"))
        self.assertIn("Mathlib.Data.Nat.Defs", res["errors"][0])
        self.assertEqual(self.probes()[0].count("import Mathlib.Data.Nat.Defs"), 1)

    def test_a_quoted_module_name_is_not_probed(self):
        res = self.check("Mathlib.Tactic.«Ring»")
        self.assertEqual((res["accepted"], res["stage"]), (False, "imports"))
        self.assertIn("plain module name", res["errors"][0])
        self.assertEqual(self.probes(), [])

    def test_the_source_lookup_reads_the_package_checkouts(self):
        pk = os.path.join(self.tmp, "ls", ".lake", "packages")
        os.makedirs(os.path.join(pk, "mathlib", "Mathlib", "Tactic"))
        open(os.path.join(pk, "mathlib", "Mathlib", "Tactic", "Ring.lean"), "w").close()
        open(os.path.join(pk, "mathlib", "Mathlib.lean"), "w").close()
        checkpy.LS_ROOT = os.path.join(self.tmp, "ls")
        self.assertTrue(_REAL_SOURCE_EXISTS("Mathlib.Tactic.Ring"))
        self.assertTrue(_REAL_SOURCE_EXISTS("Mathlib"))
        self.assertFalse(_REAL_SOURCE_EXISTS("Mathlib.Data.Nat.Defs"))

    def test_standalone_the_packages_and_manifest_are_svgolfs_own(self):
        # svGolf as its own repository: lean-surfaces is the git dependency in svGolf's
        # `.lake/packages`, beside mathlib, and the root manifest pins them (check/layout.py)
        sg = os.path.join(self.tmp, "sg")
        pk = os.path.join(sg, ".lake", "packages")
        os.makedirs(os.path.join(pk, "mathlib", "Mathlib", "Tactic"))
        os.makedirs(os.path.join(pk, "lean-models", "LeanModels", "Sv"))
        open(os.path.join(pk, "mathlib", "Mathlib", "Tactic", "Ring.lean"), "w").close()
        with open(os.path.join(sg, "lake-manifest.json"), "w") as fh:
            fh.write('{"packages": [{"name": "mathlib", "rev": "%s"}]}\n' % ("b" * 40))
        checkpy.LAYOUT, checkpy.SVGOLF = "standalone", sg
        checkpy.LS_ROOT = os.path.join(pk, "lean-models")
        with mock.patch.dict(os.environ, {"SVGOLF_PACKAGES": ""}):
            self.assertEqual(checkpy.packages_dir(), pk)
            self.assertEqual(checkpy.manifest_path(), os.path.join(sg, "lake-manifest.json"))
            self.assertTrue(_REAL_SOURCE_EXISTS("Mathlib.Tactic.Ring"))
            self.assertEqual(sorted(checkpy.package_dirs()), ["lean-models", "mathlib"])
        # inside, the same functions read lean-surfaces' (the parent's) packages and manifest
        checkpy.LAYOUT, checkpy.LS_ROOT = "inside", os.path.join(self.tmp, "ls")
        with mock.patch.dict(os.environ, {"SVGOLF_PACKAGES": ""}):
            self.assertEqual(checkpy.packages_dir(), os.path.join(self.tmp, "ls", ".lake", "packages"))
            self.assertEqual(checkpy.manifest_path(), os.path.join(self.tmp, "ls", "lake-manifest.json"))

    def test_the_allowlist_roots_are_the_package_roots(self):
        for root in checkpy.PACKAGE_ROOTS:
            self.assertTrue(any(re.fullmatch(p, root + ".X.Y") for p in checkpy.IMPORT_ALLOW), root)
        for bad in ("Cli", "Lake", "Cache.IO", "Mathlib2", "MathlibTest.Basic"):
            self.assertFalse(any(re.fullmatch(p, bad) for p in checkpy.IMPORT_ALLOW), bad)
        self.assertEqual(sorted(checkpy.PACKAGE_NAMES), sorted(checkpy.PACKAGE_ROOTS))

    def test_the_search_path_is_the_last_line_of_the_lake_output(self):
        self.assertEqual(checkpy.search_path_from("warning: x\n/a:/b::/c\n"), ["/a", "/b", "/c"])
        self.assertEqual(checkpy.search_path_from(""), [])

    def test_the_import_cross_check(self):
        parsed = ["Submission.Design", "SvGolf.Comb"]
        ok = ["Init", "Init", "Submission.Design", "SvGolf.Comb"]
        self.assertIsNone(checkpy.import_mismatch(parsed, ok))
        self.assertIsNone(checkpy.import_mismatch(["Init"] + parsed, ok))      # an explicit Init
        self.assertIn("outside the allowlist",
                      checkpy.import_mismatch(parsed, ok + ["LeanModels.Python.Semantics"]))
        self.assertIn("read differently",
                      checkpy.import_mismatch(parsed, ok + ["Mathlib.Tactic.Ring"]))   # hidden
        self.assertIn("read differently", checkpy.import_mismatch(parsed + ["Std"], ok))
        with self.assertRaises(RuntimeError):
            checkpy.import_mismatch(parsed, None)

    def test_the_comparators_import_report_is_checked_against_the_header(self):
        report = {"accepted": True, "imports": {"Submission.Solution": [
            "Init", "Init", "Submission.Design", "LeanModels.Sv.CombLib"]}}
        FakeLean.comparator = report
        res = self.check("LeanModels.Sv.CombLib")
        self.assertEqual((res["accepted"], res["stage"]), (True, "done"), res["errors"])
        # Lean read an import the checker did not
        report["imports"]["Submission.Solution"].append("Mathlib.Tactic.Ring")
        res = self.check("LeanModels.Sv.CombLib")
        self.assertEqual((res["accepted"], res["stage"]), (False, "imports"))
        self.assertIn("read differently", res["errors"][0])
        # ... one that is not even allowed
        report["imports"]["Submission.Solution"][-1] = "Examples.python.tri.proof"
        res = self.check("LeanModels.Sv.CombLib")
        self.assertEqual((res["accepted"], res["stage"]), (False, "imports"))
        self.assertIn("outside the allowlist", res["errors"][0])
        # a comparator that reports no imports is not a pass
        del report["imports"]
        with self.assertRaises(RuntimeError):
            self.check("LeanModels.Sv.CombLib")


class Tripwire(Base):
    """The REAL `integrity_snapshot` inside `check`, the staged tools stubbed out (their
    trees are not what this tests), and a parent whose manifest and package trees are temporary."""

    def setUp(self):
        super().setUp()
        self.ls = os.path.join(self.tmp, "ls")
        os.makedirs(self.ls)
        self.manifest = os.path.join(self.ls, "lake-manifest.json")
        with open(self.manifest, "w") as fh:
            fh.write('{"packages": []}\n')
        checkpy.LS_ROOT = self.ls
        checkpy._tool_trees = lambda: []
        checkpy.postsynth.trusted_files = lambda: []
        self.ring = os.path.join(self.lib, "Mathlib", "Tactic", "Ring.olean")
        for part in (".server", ".private"):
            open(self.ring + part, "w").close()
        # a report that matches the header, so that a run that is not rejected for another
        # reason is accepted
        FakeLean.comparator = {"accepted": True, "imports": {"Submission.Solution": [
            "Init", "Submission.Design"]}}

    def run_with(self, build):
        FakeLean.on_solution = build
        return self.check()

    def changed(self, res):
        return [os.path.relpath(p, self.tmp) if os.path.isabs(p) else p
                for p in res["stages"]["integrity"]["changed"]]

    def test_nothing_changed(self):
        res = self.run_with(lambda: None)
        self.assertEqual((res["accepted"], res["stage"]), (True, "done"), res["errors"])
        self.assertEqual(res["stages"]["integrity"]["changed"], [])
        self.assertEqual(res["stages"]["integrity"]["changed_by_end"], [])
        # the tripwire did watch the packages: their oleans are in the snapshot
        snap = checkpy.integrity_snapshot(os.path.join(self.tmp, "stage"), FakeLean.search_path)
        self.assertIn(self.ring, snap)
        self.assertIn(self.ring + ".private", snap)
        self.assertIn(f"search-path entry: {self.absent}", snap)

    def test_a_package_free_solution_cannot_change_a_package_olean(self):
        for target in (self.ring, self.ring + ".server", self.ring + ".private"):
            def build(target=target):
                time.sleep(0.01)
                with open(target, "a") as fh:
                    fh.write("x")
            res = self.run_with(build)
            self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"), target)
            self.assertEqual(self.changed(res), [os.path.relpath(target, self.tmp)])
            self.assertNotIn("packages", res["stages"])        # it imported no package

    def test_a_new_and_a_deleted_olean_are_seen(self):
        res = self.run_with(lambda: open(os.path.join(self.lib, "Mathlib", "Evil.olean"), "w").close())
        self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"))
        self.assertEqual(self.changed(res), [os.path.join("pk", "mathlib", ".lake", "build", "lib",
                                                          "lean", "Mathlib", "Evil.olean")])
        os.remove(os.path.join(self.lib, "Mathlib", "Evil.olean"))
        res = self.run_with(lambda: os.remove(self.ring))
        self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"))

    def test_a_search_path_entry_that_did_not_exist_cannot_be_created(self):
        # `lake env` puts Cli's build directory first and this machine has not built Cli: a
        # `Mathlib/` created there shadows Mathlib's (Lean resolves a root to the FIRST entry
        # with a directory of that name)
        def build():
            os.makedirs(os.path.join(self.absent, "Mathlib"))
            open(os.path.join(self.absent, "Mathlib", "Evil.olean"), "w").close()
        res = self.run_with(build)
        self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"))
        ch = self.changed(res)
        self.assertTrue(any(c.endswith("Evil.olean") for c in ch), ch)
        self.assertTrue(any(c.startswith("search-path entry:") and c.endswith("Cli/.lake/build/lib/lean")
                            for c in ch), ch)

    def test_an_empty_shadow_directory_is_seen_too(self):
        # no olean in it, yet `import Mathlib.Tactic.Ring` would then fail for everyone
        res = self.run_with(lambda: os.makedirs(os.path.join(self.bat, "Mathlib")))
        self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"))
        self.assertEqual(self.changed(res), [f"search-path entry: {self.bat}"])

    def test_the_manifest_that_pins_mathlib_is_watched(self):
        def build():
            with open(self.manifest, "w") as fh:
                fh.write('{"packages": [{"name": "mathlib", "rev": "x"}]}\n')
        res = self.run_with(build)
        self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"))
        self.assertEqual(self.changed(res), [os.path.relpath(self.manifest, self.tmp)])

    def test_metadata_noise_is_not_seen(self):
        def build():
            for noise in (".ilean", ".olean.hash", ".trace", ".ir"):
                with open(self.ring[:-len(".olean")] + noise, "a") as fh:
                    fh.write("noise")
        res = self.run_with(build)
        self.assertEqual((res["accepted"], res["stage"]), (True, "done"), res["errors"])

    def test_the_extractor_modules_are_watched_and_identified(self):
        # extract.py imports lower_proc.py (WP-PROC): both are fingerprinted, and the stage record's
        # `extractor_sha256` (which the leaderboard copies) is the identity of both
        snap = checkpy.integrity_snapshot(os.path.join(self.tmp, "stage"), FakeLean.search_path)
        self.assertEqual(len(checkpy.envelope.extractor_files()), 2)
        for path in checkpy.envelope.extractor_files():
            self.assertIn(path, snap)
        res = self.run_with(lambda: None)
        self.assertEqual(res["stages"]["extract"]["extractor_sha256"], checkpy.envelope.extractor_sha256())

    def test_the_walk_skips_what_other_parts_of_the_tripwire_cover(self):
        # the stage, the toolchain and the svGolf / LeanModels builds are watched elsewhere, in a
        # way that tolerates unrelated builds: the search-path walk lists their top-level names
        # only (the toolchain-like tree below has no .olean recorded)
        tc = os.path.join(self.tmp, "tc", "lib", "lean")
        os.makedirs(os.path.join(tc, "Init"))
        open(os.path.join(tc, "Init.olean"), "w").close()
        snap = checkpy.search_path_snapshot([tc, self.lib], skip=[tc])
        self.assertNotIn(os.path.join(tc, "Init.olean"), snap)
        self.assertEqual(snap[f"search-path entry: {tc}"], "names:Init.olean,Init/")
        self.assertIn(self.ring, snap)

    def test_a_package_import_after_the_tripwire_got_it_the_same_way(self):
        # the importing solution: same snapshots, plus the probe
        FakeLean.comparator["imports"]["Submission.Solution"] += ["Mathlib.Tactic.Ring"]
        def build():
            with open(self.ring, "a") as fh:
                fh.write("x")
        FakeLean.on_solution = build
        res = self.check("Mathlib.Tactic.Ring")
        self.assertEqual((res["accepted"], res["stage"]), (False, "integrity"))
        self.assertEqual(res["stages"]["packages"]["imports"], ["Mathlib.Tactic.Ring"])


class ExtractorIdentity(unittest.TestCase):
    """`envelope.extractor_sha256` (the stage record, the leaderboard) and the envelope cache key cover every file of the
    extractor, `lower_proc.py` included (WP-PROC follow-up 2)."""

    def setUp(self):
        self.env = checkpy.envelope
        self.saved = (self.env.EXTRACTOR, self.env.LOWER_PROC)
        self.tmp = tempfile.mkdtemp(prefix="extractor-identity-")
        self.extract = os.path.join(self.tmp, "extract.py")
        self.lower = os.path.join(self.tmp, "lower_proc.py")
        with open(self.extract, "w") as fh:
            fh.write("# the extractor\n")
        self.env.EXTRACTOR, self.env.LOWER_PROC = self.extract, self.lower

    def tearDown(self):
        self.env.EXTRACTOR, self.env.LOWER_PROC = self.saved
        shutil.rmtree(self.tmp, ignore_errors=True)

    def write_lower(self, text):
        with open(self.lower, "w") as fh:
            fh.write(text)

    def test_extract_py_alone_keeps_the_old_identity(self):
        # an ls-sv checkout from before lower_proc.py: the value every older record holds
        self.assertEqual(self.env.extractor_files(), [self.extract])
        self.assertEqual(self.env.extractor_sha256(), self.env.sha256_file(self.extract))

    def test_lower_proc_py_is_part_of_the_identity(self):
        alone = self.env.extractor_sha256()
        self.write_lower("# lowering v1\n")
        self.assertEqual(self.env.extractor_files(), [self.extract, self.lower])
        v1 = self.env.extractor_sha256()
        self.assertNotEqual(v1, alone)
        self.assertEqual(self.env.extractor_sha256(), v1)                 # deterministic
        self.write_lower("# lowering v2\n")
        self.assertNotEqual(self.env.extractor_sha256(), v1)              # an edit of lower_proc.py alone moves it
        with open(self.extract, "a") as fh:
            fh.write("# edited\n")
        self.assertNotEqual(self.env.extractor_sha256(), self.env.sha256_file(self.extract))

    def test_the_cache_key_follows_lower_proc_py(self):
        self.write_lower("# lowering v1\n")
        key = self.env.cache_key("module m; endmodule\n", "m", "m", [])
        self.assertEqual(key, self.env.cache_key("module m; endmodule\n", "m", "m", []))
        self.write_lower("# lowering v2\n")
        self.assertNotEqual(key, self.env.cache_key("module m; endmodule\n", "m", "m", []))


if __name__ == "__main__":
    unittest.main(verbosity=1)
