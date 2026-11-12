#!/usr/bin/env python3.12
"""Unit tests (no Lean, no Yosys, no Verilator) of check.py's small contestant
conveniences and of the checker's ADVISORY checks:

  * `dev_hint`: the command that compiles a file against the staged design,
    with the Lean wrapper in front of `lake` (an empty wrapper: unchanged text),
    also for `--unproved` runs that keep the stage;
  * `split_elapsed`: the `SVGOLF_ELAPSED <seconds>` line is parsed and removed;
  * the `--tactics` pre-check: the generated probe text for every task kind and
    the classification of the compiled probe's output (in fragment, refused with
    the tactic's own message, could not run);
  * the functional smoke check (check/postsynth.py `load_oracle`,
    `functional_check`, `functional_warning`) on synthetic ls-sv rows: counts,
    examples, the warning line, "unchecked, never a mismatch", and every task's
    oracle against independent Python arithmetic (bit-level ripple adder and
    shift-and-add multiplier; division at several formats, binary16 included,
    against the spec's exact rational oracle) on random and corner vectors;
  * the post-synthesis MODE (WP-C2): `resolve_mode` (default light, the
    environment, the flag winning, a typo is an error), `check.py`'s
    `--postsynth` and $SVGOLF_POSTSYNTH reaching `check`, `light_select`
    (a deterministic subset of the full vectors, within its budget and its
    per-class quotas), and each task's `light_vectors` budget;
  * the generated `Submission.Design` of the `design` stage (WP-C3): the
    unsupported-construct `#eval` at every probe point of every task;
  * the solution's progress (item 9 of the from-scratch study): the `trace.Kernel`
    lines read with their arrival times (`run_stamped`, `progress_summary`), dated
    from the command's start, stripped from the messages, a leak into the proof
    seen; a fake `lean` stopped at its limit through the real supervisor delivers
    them with `progress` and loses them without; the stderr lines of a timeout;
  * the replay limits (`verify_time_limit_s`, CPU seconds since 2026-11-06): a fake
    comparator and a fake `leanchecker` through the real supervisor, a burner stopped
    by the CPU limit and a sleeper by the wall-clock backstop;

    python3.12 tests/checker/test_advisories.py
"""

import contextlib
import importlib.util
import io
import json
import os
import random
import subprocess
import sys
import tempfile
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


checkpy = load("svgolf_check_py", os.path.join(SVGOLF, "check.py"))
import postsynth  # noqa: E402  (check/postsynth.py)

TASKS = os.path.join(SVGOLF, "tasks")
# the spec's exact rational oracle (its validation tooling), not the task's own oracle.py
SPEC_ORACLE = os.path.join(SVGOLF, "tasks", "fdivp", "spec_validate", "oracle.py")


def task_oracle(name):
    """(oracle function, task.json) of tasks/<name>."""
    tdir = os.path.join(TASKS, name)
    with open(os.path.join(tdir, "task.json")) as fh:
        task = json.load(fh)
    fn, why = postsynth.load_oracle(tdir, task)
    assert fn is not None, why
    return fn, task


class DevHint(unittest.TestCase):
    STAGE = "/tmp/stage"
    DESIGN_OK = {"stages": {"design": {"exit": 0, "seconds": 1.0}}}

    def test_full_run_without_wrapper_is_the_old_text(self):
        old = (f"cd {checkpy.SVGOLF} && LEAN_PATH={self.STAGE}/build "
               f"lake env lean {self.STAGE}/Submission/Solution.lean")
        self.assertEqual(checkpy.dev_hint(self.STAGE, [], False, {"stages": {}}),
                         {"dev_hint": old})

    def test_full_run_wrapper_goes_in_front_of_lake(self):
        h = checkpy.dev_hint(self.STAGE, ["/w/slot.sh"], False, {"stages": {}})["dev_hint"]
        self.assertIn(f"LEAN_PATH={self.STAGE}/build /w/slot.sh lake env lean ", h)
        h = checkpy.dev_hint(self.STAGE, ["nice", "-n", "19"], False, {"stages": {}})["dev_hint"]
        self.assertIn("build nice -n 19 lake env lean ", h)

    def test_unproved_run_probe_hint(self):
        h = checkpy.dev_hint(self.STAGE, [], True, self.DESIGN_OK)["dev_hint"]
        self.assertTrue(h.startswith(f"cd {checkpy.SVGOLF} && LEAN_PATH={self.STAGE}/build "
                                     "lake env lean <YourFile>.lean"), h)
        self.assertIn("starts with `import Submission.Design`", h)
        h = checkpy.dev_hint(self.STAGE, ["/w/slot.sh"], True, self.DESIGN_OK)["dev_hint"]
        self.assertIn(f"LEAN_PATH={self.STAGE}/build /w/slot.sh lake env lean <YourFile>.lean", h)

    def test_unproved_run_before_the_design_stage_has_no_hint(self):
        self.assertEqual(checkpy.dev_hint(self.STAGE, [], True, {"stages": {}}), {})
        self.assertEqual(checkpy.dev_hint(self.STAGE, [], True,
                                          {"stages": {"design": {"exit": 1}}}), {})


class Elapsed(unittest.TestCase):
    def test_parsed_and_removed(self):
        self.assertEqual(checkpy.split_elapsed("error: x\nSVGOLF_ELAPSED 13.79\n"),
                         ("error: x\n", 13.79))
        self.assertEqual(checkpy.split_elapsed("SVGOLF_ELAPSED 8.41\n"), ("", 8.41))

    def test_absent(self):
        self.assertEqual(checkpy.split_elapsed("plain\n"), ("plain\n", None))

    def test_the_last_reading_is_the_genuine_one(self):
        out, el = checkpy.split_elapsed("SVGOLF_ELAPSED 0.00\nerror\nSVGOLF_ELAPSED 5.50\n")
        self.assertEqual(el, 5.5)
        self.assertNotIn("SVGOLF_ELAPSED", out)


# ---------------------------------------------------------------------------
# the task oracles against independent arithmetic
# ---------------------------------------------------------------------------

def bits(x, n):
    return [(x >> i) & 1 for i in range(n)]


def ripple_add(a, b, cin, n):
    """Bit-level ripple-carry addition: (s, cout)."""
    c, s = cin, 0
    for i in range(n):
        x, y = (a >> i) & 1, (b >> i) & 1
        s |= (x ^ y ^ c) << i
        c = (x & y) | (c & (x ^ y))
    return s, c


def shift_add_mul(a, b, n):
    p = 0
    for i in range(n):
        if (b >> i) & 1:
            p += a << i
    return p


def corner_values(n):
    full = (1 << n) - 1
    return sorted({0, 1, full, full - 1 if n > 1 else 0, 1 << (n - 1), (1 << (n - 1)) - 1,
                   full >> 1, 0x5555555555555555 & full, 0xAAAAAAAAAAAAAAAA & full})


class Oracles(unittest.TestCase):
    WIDTHS = (1, 2, 3, 7, 8, 16, 31, 32, 33, 64, 100)

    def test_every_task_names_its_oracle_and_it_loads(self):
        for name in sorted(os.listdir(TASKS)):
            tdir = os.path.join(TASKS, name)
            if not os.path.isfile(os.path.join(tdir, "task.json")):
                continue
            with open(os.path.join(tdir, "task.json")) as fh:
                task = json.load(fh)
            self.assertEqual(task.get("oracle") is not None,
                             os.path.isfile(os.path.join(tdir, "oracle.py")), name)
            if task.get("oracle"):
                fn, why = postsynth.load_oracle(tdir, task)
                self.assertIsNotNone(fn, f"{name}: {why}")

    def test_add(self):
        fn, _ = task_oracle("add")
        rng = random.Random(1)
        for n in self.WIDTHS:
            vals = corner_values(n) + [rng.getrandbits(n) for _ in range(60)]
            for a in vals:
                for b in rng.sample(vals, 8):
                    for cin in (0, 1):
                        out = fn({"N": n}, {"a": a, "b": b, "cin": cin})
                        self.assertEqual(set(out), {"s", "cout"})
                        self.assertEqual((out["s"], out["cout"]), ripple_add(a, b, cin, n))
                        self.assertEqual(out["cout"] * 2 ** n + out["s"], a + b + cin)

    def test_mul(self):
        fn, _ = task_oracle("mul")
        rng = random.Random(2)
        for n in self.WIDTHS:
            vals = corner_values(n) + [rng.getrandbits(n) for _ in range(40)]
            for a in vals:
                for b in rng.sample(vals, 8):
                    out = fn({"N": n}, {"a": a, "b": b})
                    self.assertEqual(set(out), {"p"})
                    self.assertEqual(out["p"], shift_add_mul(a, b, n))
                    self.assertLess(out["p"], 2 ** (2 * n))

    def test_clmul(self):
        """The carry-less product, against Kronecker substitution (integer multiplication of the
        bit-spread operands, read the parity of each group): a different algorithm from the oracle's
        shift-and-XOR."""
        fn, _ = task_oracle("clmul")
        rng = random.Random(4)
        for n in self.WIDTHS:
            vals = corner_values(n) + [rng.getrandbits(n) for _ in range(40)]
            k = n.bit_length() + 1                  # a group sums at most n ones: no carry leaves it
            def spread(x):
                return sum(((x >> i) & 1) << (k * i) for i in range(n))
            for a in vals:
                for b in rng.sample(vals, 8):
                    out = fn({"N": n}, {"a": a, "b": b})
                    self.assertEqual(set(out), {"p"})
                    prod = spread(a) * spread(b)
                    self.assertEqual(out["p"], sum(((prod >> (k * j)) & 1) << j for j in range(2 * n - 1)))
                    self.assertLess(out["p"], 2 ** (2 * n - 1))

    def test_example(self):
        fn, _ = task_oracle("_example")
        rng = random.Random(3)
        for n in self.WIDTHS:
            for _ in range(50):
                a, b = rng.getrandbits(n), rng.getrandbits(n)
                self.assertEqual(fn({"N": n}, {"a": a, "b": b}),
                                 {"y": sum(((x & y) << i) for i, (x, y) in
                                           enumerate(zip(bits(a, n), bits(b, n))))})

    def test_fdivp_against_the_spec_oracle_at_several_formats(self):
        """The parametric oracle (exact Fractions, written separately) against spec/validate/oracle.py's
        `div_exact` at formats other than binary16: every pair of two small formats and corner-rich samples
        of binary32, bfloat16-like, binary64 and two skewed formats."""
        fn, _ = task_oracle("fdivp")
        spec_oracle = load("svgolf_spec_oracle_test_p", SPEC_ORACLE)
        for w, p in ((2, 2), (2, 3)):
            n, fmt = 1 << (w + p), spec_oracle.Fmt(w, p)
            for a in range(n):
                for b in range(n):
                    self.assertEqual(fn({"W": w, "P": p}, {"a": a, "b": b})["q"],
                                     spec_oracle.div_exact(fmt, a, b), (w, p, a, b))
        rng = random.Random(9)
        for w, p in ((3, 4), (5, 11), (8, 24), (8, 8), (11, 53), (2, 30), (3, 20)):
            k, fmt = w + p, spec_oracle.Fmt(w, p)
            pats = [0, 1, (1 << (k - 1)), ((1 << w) - 1) << (p - 1), (((1 << w) - 1) << (p - 1)) | 1,
                    (1 << (p - 1)) - 1, 1 << (p - 1), ((1 << (w - 1)) - 1) << (p - 1)]
            pairs = [(a, b) for a in pats for b in pats]
            pairs += [(rng.getrandbits(k), rng.getrandbits(k)) for _ in range(100)]
            for a, b in pairs:
                out = fn({"W": w, "P": p}, {"a": a, "b": b})
                self.assertEqual(set(out), {"q"})
                self.assertEqual(out["q"], spec_oracle.div_exact(fmt, a, b), (w, p, a, b))

    def test_fdivp_binary16_against_the_spec_oracle(self):
        """binary16, the instance (W, P) = (5, 11) (the scoring point; the rows of the former 16-bit task's oracle
        test): the 18 x 18 special operands of task.json's postsynth corners, random pairs, and subnormal results
        including the exact ties (x / 2^k for tiny x)."""
        fn, task = task_oracle("fdivp")
        spec_oracle = load("svgolf_spec_oracle_test_16", SPEC_ORACLE)
        special = [0x0000, 0x8000, 0x0001, 0x8001, 0x03FF, 0x0400, 0x3C00, 0xBC00, 0x3BFF, 0x7BFF,
                   0xFBFF, 0x7C00, 0xFC00, 0x7C01, 0x7E00, 0xFE00, 0x4000, 0x3FFF]
        corners = task["postsynth"]["corners"]
        self.assertEqual([int(x, 16) for x in corners["a"]], special)
        self.assertEqual([int(x, 16) for x in corners["b"]], special)
        rng = random.Random(4)
        pairs = [(a, b) for a in special for b in special]
        pairs += [(rng.getrandbits(16), rng.getrandbits(16)) for _ in range(1500)]
        pairs += [(rng.randrange(1, 0x0400), rng.choice([0x4000, 0x4400, 0x4800, 0x7BFF]))
                  for _ in range(300)]
        for a, b in pairs:
            out = fn({"W": 5, "P": 11}, {"a": a, "b": b})
            self.assertEqual(set(out), {"q"})
            self.assertEqual(out["q"], spec_oracle.div_exact(spec_oracle.BINARY16, a, b),
                             f"a={a:#06x} b={b:#06x}")


# ---------------------------------------------------------------------------
# the comparison on synthetic ls-sv rows
# ---------------------------------------------------------------------------

INS = [("a", 4), ("b", 4), ("cin", 1)]
OUTS = [("cout", 1), ("s", 4)]          # postsynth sorts both lists by port name
ADD_FN = None


def add_oracle(params, inputs):
    t = inputs["a"] + inputs["b"] + inputs["cin"]
    return {"s": t % 16, "cout": t >> 4}


def vectors(k=40, seed=7):
    rng = random.Random(seed)
    return [{"a": rng.getrandbits(4), "b": rng.getrandbits(4), "cin": rng.getrandbits(1)}
            for _ in range(k)]


def lssv_row(v, wrong=None):
    """ls-sv's pair of states for vector `v` of the correct adder; `wrong` flips s[0]."""
    t = v["a"] + v["b"] + v["cin"]
    s = t % 16 ^ (1 if wrong else 0)
    row = {"cout": format(t >> 4, "b"), "s": format(s, "04b")}
    return (dict(row), dict(row))


class Functional(unittest.TestCase):
    PARAMS = {"N": 4}

    def check(self, vecs, rows, oracle=(add_oracle, None)):
        return postsynth.functional_check(oracle, self.PARAMS, "N=4", INS, OUTS, vecs, rows)

    def test_a_correct_design_has_no_mismatch(self):
        vecs = vectors()
        f = self.check(vecs, [lssv_row(v) for v in vecs])
        self.assertEqual(f, {"checked": 40, "mismatches": 0, "examples": []})
        self.assertIsNone(postsynth.functional_warning(f))

    def test_mismatches_are_counted_and_the_first_three_listed(self):
        vecs = vectors()
        bad = {3, 5, 9, 11, 20}
        f = self.check(vecs, [lssv_row(v, wrong=i in bad) for i, v in enumerate(vecs)])
        self.assertEqual((f["checked"], f["mismatches"]), (40, 5))
        self.assertEqual(set(f), {"checked", "mismatches", "examples"})
        self.assertEqual(len(f["examples"]), 3)
        first = f["examples"][0]
        self.assertEqual(set(first), {"point", "inputs", "expected", "got"})
        self.assertEqual(first["point"], "N=4")
        v = vecs[3]
        self.assertEqual(first["inputs"], {"a": hex(v["a"]), "b": hex(v["b"]), "cin": hex(v["cin"])})
        t = v["a"] + v["b"] + v["cin"]
        self.assertEqual(first["expected"], {"cout": hex(t >> 4), "s": hex(t % 16)})
        self.assertEqual(first["got"], {"cout": hex(t >> 4), "s": hex(t % 16 ^ 1)})
        # the examples are the first mismatches in vector order
        self.assertEqual([e["inputs"]["a"] for e in f["examples"]],
                         [hex(vecs[i]["a"]) for i in (3, 5, 9)])

    def test_the_warning_is_one_line(self):
        vecs = vectors()
        f = self.check(vecs, [lssv_row(v, wrong=True) for v in vecs])
        w = postsynth.functional_warning(f)
        self.assertNotIn("\n", w)
        v = vecs[0]
        t = v["a"] + v["b"] + v["cin"]
        self.assertEqual(
            w, "functional: the design disagrees with the task's function on 40 of 40 vectors; "
            f"first: a={hex(v['a'])} b={hex(v['b'])} cin={hex(v['cin'])} "
            f"expected s={hex(t % 16)} got s={hex(t % 16 ^ 1)} "
            "(an advisory check: the Lean proof is the authority, but a design that computes "
            "something else cannot have one)")

    def test_ls_sv_errors_and_x_are_unchecked_not_mismatches(self):
        vecs = vectors(10)
        rows = [lssv_row(v) for v in vecs]
        rows[1] = ("ERROR", "TIMEOUT")
        rows[2] = ({"cout": "x", "s": "0000"}, {"cout": "x", "s": "0000"})
        rows[3] = ({"s": "0000"}, {"s": "0000"})              # an output missing
        f = self.check(vecs, rows)
        self.assertEqual((f["checked"], f["mismatches"], f["unchecked"]), (7, 0, 3))
        self.assertNotIn("note", f)

    def test_an_oracle_fault_is_unchecked_not_a_mismatch(self):
        vecs = vectors(10)
        rows = [lssv_row(v) for v in vecs]

        def raises(params, inputs):
            raise RuntimeError("boom")
        for label, fn in (("raises", raises),
                          ("wrong ports", lambda p, i: {"s": 0}),
                          ("extra port", lambda p, i: {"s": 0, "cout": 0, "z": 0}),
                          ("out of range", lambda p, i: {"s": 16, "cout": 0}),
                          ("negative", lambda p, i: {"s": -1, "cout": 0}),
                          ("bool", lambda p, i: {"s": True, "cout": False}),
                          ("not a dict", lambda p, i: (0, 0))):
            f = self.check(vecs, rows, (fn, None))
            self.assertEqual((f["checked"], f["mismatches"], f["unchecked"]), (0, 0, 10), label)
            self.assertIn("note", f, label)
            self.assertIsNone(postsynth.functional_warning(f), label)

    def test_an_oracle_that_did_not_load_is_all_unchecked(self):
        vecs = vectors(10)
        f = self.check(vecs, [lssv_row(v) for v in vecs], (None, "it does not load"))
        self.assertEqual(f, {"checked": 0, "mismatches": 0, "examples": [], "unchecked": 10,
                             "note": "it does not load"})

    def test_the_oracle_gets_copies(self):
        seen = []

        def spy(params, inputs):
            params["N"] = 99
            inputs["a"] = 99
            seen.append(1)
            return add_oracle({}, {"a": 0, "b": 0, "cin": 0})
        vecs = vectors(5)
        self.check(vecs, [lssv_row(v) for v in vecs], (spy, None))
        self.assertEqual(self.PARAMS, {"N": 4})
        self.assertTrue(all(v["a"] < 16 for v in vecs))


class LoadOracle(unittest.TestCase):
    def load(self, files, task):
        with tempfile.TemporaryDirectory() as d:
            for name, text in files.items():
                with open(os.path.join(d, name), "w") as fh:
                    fh.write(text)
            return postsynth.load_oracle(d, dict(task, name="t"))

    def test_no_oracle_means_no_check(self):
        self.assertEqual(self.load({}, {}), (None, None))
        self.assertEqual(postsynth.load_oracle(None, {"oracle": "oracle.py"}), (None, None))

    def test_a_good_oracle(self):
        fn, why = self.load({"oracle.py": "def oracle(params, inputs):\n    return {'y': 1}\n"},
                            {"oracle": "oracle.py"})
        self.assertIsNone(why)
        self.assertEqual(fn({}, {}), {"y": 1})

    def test_faults_are_reasons_never_exceptions(self):
        for files, task in (({}, {"oracle": "oracle.py"}),
                            ({"oracle.py": "raise ValueError('x')\n"}, {"oracle": "oracle.py"}),
                            ({"oracle.py": "def f(): pass\n"}, {"oracle": "oracle.py"}),
                            ({"oracle.py": "oracle = 3\n"}, {"oracle": "oracle.py"}),
                            ({"oracle.py": "def oracle(p, i): pass\n"}, {"oracle": "../oracle.py"})):
            fn, why = self.load(files, task)
            self.assertIsNone(fn)
            self.assertTrue(why)


# ---------------------------------------------------------------------------
# `--tactics`
# ---------------------------------------------------------------------------

class Tactics(unittest.TestCase):
    P = "/var/x/svgolf-check-ab/Submission/TacticsProbe.lean"

    def test_probe_text_per_task_kind(self):
        for name in ("add", "mul", "_example"):
            with open(os.path.join(TASKS, name, "task.json")) as fh:
                task = json.load(fh)
            text = checkpy.tactics_probe_text(task)
            self.assertIn("import Submission.Design\n", text)
            self.assertIn("example (N : Nat) : LeanModels.Sv.CombDesign (design.sem N) := by\n"
                          "  sv_structure?\n", text, name)
            self.assertNotIn("sorry", text)
        with open(os.path.join(TASKS, "aes_sbox", "task.json")) as fh:
            fixed = json.load(fh)
        self.assertIn("example : LeanModels.Sv.CombDesign design.sem := by\n  sv_structure?\n",
                      checkpy.tactics_probe_text(fixed))
        # not a combinational task, or a parameter list the probe cannot state: no probe
        self.assertIsNone(checkpy.tactics_probe_text({"name": "x", "kind": "seq"}))
        self.assertIsNone(checkpy.tactics_probe_text({"name": "x", "kind": "comb-family",
                                                      "parameters": []}))
        # two parameters (`fdivp`): one binder each, in declaration order
        with open(os.path.join(TASKS, "fdivp", "task.json")) as fh:
            two = json.load(fh)
        self.assertIn("example (W : Nat) (P : Nat) : LeanModels.Sv.CombDesign (design.sem W P) := by\n"
                      "  sv_structure?\n", checkpy.tactics_probe_text(two))
        # a parameter name that is not a plain identifier gets a plain binder
        odd = {"name": "x", "kind": "comb-family", "parameters": [{"name": "W'1"}]}
        self.assertIn("example (n : Nat) : LeanModels.Sv.CombDesign (design.sem n)",
                      checkpy.tactics_probe_text(odd))

    def test_in_fragment(self):
        out = (f"{self.P}:12:0: info: declarations: ...\n"
               f"{self.P}:12:2: error: unsolved goals\nN : Nat\n⊢ CombDesign (design.sem N)\n")
        self.assertEqual(checkpy.classify_tactics_output(1, out),
                         {"in_fragment": True, "message": "ok"})
        self.assertEqual(checkpy.classify_tactics_output(0, ""),
                         {"in_fragment": True, "message": "ok"})

    def test_refused_with_the_tactics_own_first_line(self):
        out = (f"{self.P}:12:2: error: sv_structure: outside the supported fragment — site "
               "`g_bit#2`: conditional expression `?:` (outside the v1 fragment)\n"
               f"{self.P}:12:2: error: unsolved goals\n")
        self.assertEqual(
            checkpy.classify_tactics_output(1, out),
            {"in_fragment": False, "message": "sv_structure: outside the supported fragment — "
             "site `g_bit#2`: conditional expression `?:` (outside the v1 fragment)"})
        out = f"{self.P}:12:2: error: sv_structure: cannot read a `load_design_sv2` family\n"
        self.assertFalse(checkpy.classify_tactics_output(1, out)["in_fragment"])

    def test_could_not_run_is_null_never_a_verdict(self):
        t = checkpy.classify_tactics_output(
            1, f"{self.P}:1:0: error: unknown module prefix 'LeanModels'\n")
        self.assertIsNone(t["in_fragment"])
        self.assertIn("unknown module prefix", t["message"])
        t = checkpy.classify_tactics_output(1, "lean: out of memory\n")
        self.assertIsNone(t["in_fragment"])
        self.assertIn("out of memory", t["message"])
        t = checkpy.classify_tactics_output(124, "SVGOLF_TIMEOUT after 300s\n")
        self.assertIsNone(t["in_fragment"])
        self.assertIn("did not finish", t["message"])


class ModeSelection(unittest.TestCase):
    """`postsynth.resolve_mode` and how check.py passes the mode on."""

    def test_default_is_light(self):
        self.assertEqual(postsynth.DEFAULT_MODE, "light")
        self.assertEqual(postsynth.resolve_mode(None, {}), "light")
        self.assertEqual(postsynth.resolve_mode(environ={"SVGOLF_POSTSYNTH": ""}), "light")

    def test_environment_and_flag(self):
        env = {"SVGOLF_POSTSYNTH": "full"}
        self.assertEqual(postsynth.resolve_mode(None, env), "full")
        self.assertEqual(postsynth.resolve_mode("light", env), "light")      # the flag wins
        self.assertEqual(postsynth.resolve_mode("full", {"SVGOLF_POSTSYNTH": "light"}), "full")
        self.assertEqual(postsynth.resolve_mode(None, {"SVGOLF_POSTSYNTH": "light"}), "light")

    def test_a_typo_is_an_error_not_the_default(self):
        for bad in ("Full", "FULL", "fast", "0", " full"):
            with self.assertRaises(postsynth.InfraError) as cm:
                postsynth.resolve_mode(None, {"SVGOLF_POSTSYNTH": bad})
            self.assertIn("SVGOLF_POSTSYNTH", str(cm.exception))
            with self.assertRaises(postsynth.InfraError):
                postsynth.resolve_mode(bad, {})

    def test_the_environment_is_read_when_no_environ_is_given(self):
        old = os.environ.get("SVGOLF_POSTSYNTH")
        try:
            os.environ["SVGOLF_POSTSYNTH"] = "full"
            self.assertEqual(postsynth.resolve_mode(), "full")
            del os.environ["SVGOLF_POSTSYNTH"]
            self.assertEqual(postsynth.resolve_mode(), "light")
        finally:
            if old is None:
                os.environ.pop("SVGOLF_POSTSYNTH", None)
            else:
                os.environ["SVGOLF_POSTSYNTH"] = old

    def run_main(self, argv, env=None):
        """check.py's `main` with `check` replaced by a recorder: (exit, mode it got)."""
        seen = []

        def fake_check(*a, **kw):
            seen.append(a[11] if len(a) > 11 else kw.get("postsynth_mode"))
            return {"accepted": False, "stage": "unproved", "errors": [], "stages": {}}
        old = os.environ.get("SVGOLF_POSTSYNTH")
        os.environ.pop("SVGOLF_POSTSYNTH", None)
        if env is not None:
            os.environ["SVGOLF_POSTSYNTH"] = env
        try:
            with mock.patch.object(checkpy, "check", fake_check), \
                    contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                try:
                    rc = checkpy.main(argv)
                except SystemExit as e:
                    rc = e.code
        finally:
            os.environ.pop("SVGOLF_POSTSYNTH", None)
            if old is not None:
                os.environ["SVGOLF_POSTSYNTH"] = old
        return rc, (seen[0] if seen else None)

    ARGV = [os.path.join(SVGOLF, "tasks", "_example"),
            os.path.join(SVGOLF, "tests", "_example", "attacks", "z_rare.sv"), "--unproved"]

    def test_check_py_default_flag_and_environment(self):
        self.assertEqual(self.run_main(self.ARGV), (1, "light"))
        self.assertEqual(self.run_main(self.ARGV, env="full"), (1, "full"))
        self.assertEqual(self.run_main(self.ARGV + ["--postsynth", "full"]), (1, "full"))
        self.assertEqual(self.run_main(self.ARGV + ["--postsynth", "light"], env="full"),
                         (1, "light"))
        self.assertEqual(self.run_main(self.ARGV + ["--postsynth", "full"], env="light"),
                         (1, "full"))

    def test_check_py_refuses_a_bad_mode(self):
        self.assertEqual(self.run_main(self.ARGV + ["--postsynth", "fast"]), (2, None))
        self.assertEqual(self.run_main(self.ARGV, env="fast"), (2, None))     # before any work

    def test_the_checks_own_default_resolves_too(self):
        # check() called directly (tests, other tools) resolves None the same way
        with self.assertRaises(RuntimeError):
            old = os.environ.get("SVGOLF_POSTSYNTH")
            os.environ["SVGOLF_POSTSYNTH"] = "fast"
            try:
                checkpy.check("/nonexistent", "/nonexistent.sv", None, "/tmp/x", [])
            finally:
                if old is None:
                    os.environ.pop("SVGOLF_POSTSYNTH", None)
                else:
                    os.environ["SVGOLF_POSTSYNTH"] = old


def synthetic_vectors(ins, n, seed=3):
    rng = random.Random(seed)
    return [{k: rng.getrandbits(w) for k, w in ins} for _ in range(n)]


class LightSelect(unittest.TestCase):
    """`postsynth.light_select`: the light vector set is a deterministic subset of the full
    one, within its budget, with the per-class quotas of the module docstring."""
    INS = [("a", 16), ("b", 16)]

    def lists(self, corners=None, n_assign=5, n_pairs=7, n_rand=60):
        fixed, nfixed = postsynth.fixed_vectors(self.INS, corners or {})
        f = len(postsynth.HARVEST_FILLS)
        harvest = synthetic_vectors(self.INS, f * (n_assign + n_pairs), seed=11)
        rand = synthetic_vectors(self.INS, n_rand, seed=5)
        return fixed, nfixed, harvest, n_assign, rand

    def test_spread(self):
        self.assertEqual(postsynth.spread(list(range(10)), 0), [])
        self.assertEqual(postsynth.spread(list(range(5)), 9), list(range(5)))
        got = postsynth.spread(list(range(100)), 7)
        self.assertEqual(len(got), 7)
        self.assertEqual(got[0], 0)
        self.assertEqual(got, sorted(set(got)))
        self.assertEqual(postsynth.spread(list(range(100)), 1), [0])

    def test_a_subset_within_the_budget_with_the_corner_vectors_first(self):
        fixed, nfixed, harvest, nu, rand = self.lists()
        for total in (6, 12, 40, 100, 256, 1000):
            vs, counts = postsynth.light_select(fixed, nfixed, harvest, nu, rand, total)
            full = fixed + harvest + rand
            keys = lambda xs: [tuple(v[n] for n, _ in self.INS) for v in xs]   # noqa: E731
            self.assertTrue(set(keys(vs)) <= set(keys(full)), total)
            self.assertLessEqual(len(vs), max(total, 2), total)
            self.assertEqual(keys(vs[:2]), keys(fixed[:2]))                # all-0, all-1
            self.assertEqual(sum(counts.values()), len(vs))
            self.assertEqual(counts["fixed"] + counts["task_corners"] + counts["harvest_vectors"]
                             + counts["random"], len(vs))

    def test_quotas(self):
        fixed, nfixed, harvest, nu, rand = self.lists(corners={"a": [0, 1, 2, 3, 0xFFFF],
                                                               "b": [0, 5, 0xFFFF]}, n_rand=500)
        total = 66
        q = (total - 2) // 4                  # 16
        vs, c = postsynth.light_select(fixed, nfixed, harvest, nu, rand, total)
        self.assertEqual(c["fixed"], 2 + q)                # all-0, all-1, q of the walking ones
        self.assertEqual(c["task_corners"], 15)            # all 5 x 3 corner products fit the quota
        self.assertLessEqual(c["harvest_vectors"], q)
        self.assertEqual(len(vs), total)                   # the random vectors fill the rest
        self.assertGreaterEqual(c["random"], q)

    def test_what_a_class_does_not_use_goes_to_random(self):
        fixed, nfixed, harvest, nu, rand = self.lists(n_assign=0, n_pairs=0, n_rand=400)
        vs, c = postsynth.light_select(fixed, nfixed, [], 0, rand, 100)
        self.assertEqual((c["task_corners"], c["harvest_vectors"]), (0, 0))
        self.assertEqual(len(vs), 100)
        self.assertEqual(c["random"], 100 - c["fixed"])

    def test_the_random_vectors_are_the_first_of_the_stream(self):
        fixed, nfixed, harvest, nu, rand = self.lists(n_rand=300)
        vs, c = postsynth.light_select(fixed, nfixed, harvest, nu, rand, 100)
        tail = vs[len(vs) - c["random"]:]
        self.assertEqual(tail, rand[:c["random"]])

    def test_harvest_takes_the_zero_and_one_fills_singles_before_pairs(self):
        fixed, nfixed, harvest, nu, rand = self.lists(n_assign=3, n_pairs=4)
        f = len(postsynth.HARVEST_FILLS)
        vs, c = postsynth.light_select(fixed, nfixed, harvest, nu, rand, 258)     # quota 64
        taken = vs[c["fixed"] + c["task_corners"]:][:c["harvest_vectors"]]
        want = [harvest[b * f + j] for b in range(3 + 4) for j in (0, 1)]
        self.assertEqual(taken, want)                      # 3 singles, then the 4 pairs
        # a budget under the singles' own 0/1 fills: only singles, evenly spread
        vs, c = postsynth.light_select(fixed, nfixed, harvest, nu, rand, 2 + 4 * 4)
        taken = vs[c["fixed"] + c["task_corners"]:][:c["harvest_vectors"]]
        self.assertEqual(c["harvest_vectors"], 4)
        singles = [harvest[b * f + j] for b in range(3) for j in (0, 1)]
        self.assertTrue(all(v in singles for v in taken))

    def test_deterministic(self):
        a = self.lists()
        self.assertEqual(postsynth.light_select(*a, 90), postsynth.light_select(*a, 90))

    def test_a_bad_light_budget_is_refused(self):
        for bad in (0, 5, -3, 12.5, "256", True, None):
            with self.assertRaises(postsynth.InfraError, msg=repr(bad)):
                postsynth.config({"postsynth": {"light_vectors": bad}})
        self.assertEqual(postsynth.config({"postsynth": {"light_vectors": 6}})["light_vectors"], 6)
        self.assertEqual(postsynth.config({})["light_vectors"], 256)

    def test_every_tasks_light_budget_is_a_valid_integer(self):
        for name in os.listdir(TASKS):
            tdir = os.path.join(TASKS, name)
            if not os.path.isfile(os.path.join(tdir, "task.json")):
                continue
            with open(os.path.join(tdir, "task.json")) as fh:
                cfg = postsynth.config(json.load(fh))
            if "light_vectors" not in cfg:       # a clocked kind: no vector budget (postsynth.CLOCKED_DEFAULTS)
                self.assertIn("seeds", cfg, name)
                continue
            self.assertIsInstance(cfg["light_vectors"], int, name)
            self.assertGreaterEqual(cfg["light_vectors"], 6, name)
            self.assertLessEqual(cfg["light_vectors"], 1000, name)


class DesignModuleText(unittest.TestCase):
    """The generated `Submission.Design` (WP-C3): after `load_design_sv2`, an `#eval` that
    rejects an unsupported node at every point the extractor cross-checked."""

    def text(self, name):
        with open(os.path.join(TASKS, name, "task.json")) as fh:
            return checkpy.design_module_text(json.load(fh), "/x/env.json")

    def test_family_task_checks_the_scoring_point_and_the_smaller_probe_points(self):
        t = self.text("add")
        for pt in ("N=1", "N=2", "N=3", "N=16"):
            self.assertIn(f'("{pt}", design.sem {pt.split("=")[1]})', t)
        for pt in ("N=32", "N=64"):                  # above the scoring point: skipped for cost
            self.assertNotIn(f'("{pt}"', t)
        self.assertLess(t.index('("N=16"'), t.index('("N=1"'))      # the scoring point first
        self.assertIn("d.hasUnsupported", t)
        self.assertIn("d.firstLoud", t)
        self.assertIn("SVGOLF_UNSUPPORTED at", t)
        self.assertIn("SVGOLF_UNSUPPORTED_FREE", t)
        self.assertLess(t.index("abbrev Goal"), t.index("#eval"))

    def test_scoring_point_is_always_in_and_first(self):
        for name in ("add", "mul", "_example"):
            with open(os.path.join(TASKS, name, "task.json")) as fh:
                task = json.load(fh)
            pts = checkpy.unsupported_check_points(task)
            self.assertEqual(pts[0], {"N": 16}, name)
            self.assertTrue(all(p["N"] <= 16 for p in pts), name)
            self.assertEqual(len(pts), len({p["N"] for p in pts}), name)
            t = checkpy.unsupported_check_text(task)
            self.assertEqual(t.count("design.sem"), len(pts), name)
            self.assertIn('("N=16", design.sem 16)', t)
        with open(os.path.join(TASKS, "mul", "task.json")) as fh:
            self.assertEqual([p["N"] for p in checkpy.unsupported_check_points(json.load(fh))],
                             [16, 1, 2, 3, 4, 8])      # not 32

    def test_fixed_size_task_has_the_one_design(self):
        t = self.text("aes_sbox")
        self.assertIn('("default", design.sem)', t)
        self.assertEqual(t.count("design.sem"), 2)    # the statement and the list entry

    def test_markers_parse(self):
        m = checkpy.UNSUPPORTED_AT.search("x\nSVGOLF_UNSUPPORTED at N=16: Call:f: both(a, b)\n")
        self.assertEqual(m.group(1), "N=16: Call:f: both(a, b)")
        self.assertEqual(checkpy.UNSUPPORTED_FREE.search("SVGOLF_UNSUPPORTED_FREE 6").group(1), "6")
        self.assertIsNone(checkpy.UNSUPPORTED_FREE.search("nothing"))


# ---------------------------------------------------------------------------
# what a newcomer reads (the 11/05 newcomer study): the first Lean errors, the exit status of a clean
# `--unproved` run, the ranked headline, the stage lines, the wrapper's wait and SVGOLF_LEAN_WRAP_ONCE
# ---------------------------------------------------------------------------

def lean_output(n_errors, dump=900):
    """A Lean output like a failed proof's: each error's first line, then a long goal dump."""
    out = []
    for i in range(n_errors):
        out.append(f"/tmp/stage/Submission/Solution.lean:{10 + i}:4: error: Tactic `rewrite` failed number {i}")
        out.append("  st.boolAt \"c\" 1 = " + "x && " * (dump // 5))
    return "\n".join(out) + "\n"


class ErrorsFirst(unittest.TestCase):
    """B2: `errors` keeps the FIRST Lean errors (a tail kept only the last error's goal dump)."""

    def test_short_output_is_unchanged(self):
        text = lean_output(2, dump=50)
        self.assertEqual(checkpy.errors_first(text), text)

    def test_every_error_line_comes_first_then_the_tail(self):
        text = lean_output(8)
        self.assertGreater(len(text), 4000)
        got = checkpy.errors_first(text)
        self.assertLessEqual(len(got), 4000 + 400)
        self.assertNotIn("number 0", checkpy.tail(text))        # what the plain tail lost
        for i in range(8):
            self.assertIn(f"Solution.lean:{10 + i}:4: error: Tactic `rewrite` failed number {i}", got)
        self.assertLess(got.index("number 0"), got.index("number 7"))
        self.assertTrue(got.startswith("the errors (8, the first line of each):\n"), got[:80])
        self.assertTrue(got.endswith(text[-150:]))                 # and the end of the output

    def test_the_list_is_capped(self):
        text = lean_output(60, dump=100)
        got = checkpy.errors_first(text)
        self.assertLessEqual(len(got), 4000 + 400)
        self.assertIn("number 0", got)
        self.assertRegex(got.splitlines()[0], r"^the errors \(60, the first line of each; \d+ more not listed\):$")

    def test_no_error_line_is_the_plain_tail(self):
        text = "warning: x\n" * 1000
        self.assertEqual(checkpy.errors_first(text), checkpy.tail(text))


class WrapPlan(unittest.TestCase):
    """Item 9: SVGOLF_LEAN_WRAP_ONCE=1 takes the wrapper once for the whole run; per call stays the default."""

    def test_modes(self):
        w = ["/w/slot.sh"]
        self.assertEqual(checkpy.lean_wrap_plan(w, {})["mode"], "per-call")
        self.assertEqual(checkpy.lean_wrap_plan(w, {})["call"], w)
        self.assertEqual(checkpy.lean_wrap_plan([], {})["mode"], "none")
        self.assertEqual(checkpy.lean_wrap_plan([], {"SVGOLF_LEAN_WRAP_ONCE": "1"})["mode"], "none")
        self.assertEqual(checkpy.lean_wrap_plan(w, {"SVGOLF_LEAN_WRAP_ONCE": "0"})["mode"], "per-call")
        once = checkpy.lean_wrap_plan(w, {"SVGOLF_LEAN_WRAP_ONCE": "1"})
        self.assertEqual((once["mode"], once["call"]), ("once", w))

    def test_the_run_behind_the_wrapper_calls_lean_directly_and_its_hint_keeps_the_wrapper(self):
        p = checkpy.lean_wrap_plan(["/w/slot.sh"], {"SVGOLF_LEAN_WRAP_ONCE": "1", "SVGOLF_LEAN_WRAP_HELD": "/w/slot.sh -q",
                                                    "SVGOLF_LEAN_WRAP_SINCE": "100.5"})
        self.assertEqual(p, {"mode": "inside", "call": [], "hint": ["/w/slot.sh", "-q"], "since": 100.5})
        h = checkpy.dev_hint("/tmp/stage", p["hint"], False, {"stages": {}})["dev_hint"]
        self.assertIn("LEAN_PATH=/tmp/stage/build /w/slot.sh -q lake env lean ", h)

    def test_once_end_to_end_takes_the_wrapper_once(self):
        """check.py itself (no Lean: the source gate refuses the design): the wrapper is started ONCE, around check.py,
        the run inside it says so, and its exit status is the run's."""
        tmp = tempfile.mkdtemp(prefix="svgolf-once-")
        self.addCleanup(lambda: __import__("shutil").rmtree(tmp, ignore_errors=True))
        log, wrapper = os.path.join(tmp, "calls.log"), os.path.join(tmp, "wrap.sh")
        with open(wrapper, "w") as fh:
            fh.write(f'#!/bin/sh\necho "$@" >> {log}\nexec "$@"\n')
        os.chmod(wrapper, 0o755)
        bad = os.path.join(tmp, "bad.sv")
        with open(bad, "w") as fh:
            fh.write("`define X 1\nmodule band #(parameter N = 16) (input [N-1:0] a, b, output [N-1:0] y);\n"
                     "  assign y = a & b;\nendmodule\n")
        env = dict(os.environ, SVGOLF_LEAN_WRAP=wrapper, SVGOLF_LEAN_WRAP_ONCE="1")
        for k in ("SVGOLF_LEAN_WRAP_HELD", "SVGOLF_LEAN_WRAP_SINCE"):
            env.pop(k, None)
        import subprocess
        proc = subprocess.run([sys.executable, os.path.join(SVGOLF, "check.py"), os.path.join(TASKS, "_example"), bad,
                               "--unproved", "--no-trusted-build", "--sandbox", "off", "--ppa", "off"],
                              capture_output=True, text=True, env=env)
        res = json.loads(proc.stdout)
        self.assertEqual((proc.returncode, res["stage"]), (1, "source"), proc.stderr)
        with open(log) as fh:
            calls = fh.read().splitlines()
        self.assertEqual(len(calls), 1, calls)
        self.assertIn(os.path.join(SVGOLF, "check.py"), calls[0])
        self.assertEqual(set(res["lean_wrap"]), {"once", "waited"})
        self.assertTrue(res["lean_wrap"]["once"])
        self.assertIn("check: lean wrapper ... (taken once for the whole run", proc.stderr)


class FakeWrapperLean(unittest.TestCase):
    """B7: a stage's `seconds` exclude the wait in the wrapper (the untimed `lake build` included); the wait is
    reported apart. A wrapper that sleeps, and a `lake` that answers at once (no Lean)."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="svgolf-wait-")
        self.addCleanup(lambda: __import__("shutil").rmtree(self.tmp, ignore_errors=True))
        bindir = os.path.join(self.tmp, "bin")
        os.makedirs(bindir)
        with open(os.path.join(bindir, "lake"), "w") as fh:
            fh.write('#!/bin/sh\nif [ "$1" = env ]; then shift; exec "$@"; fi\necho "lake $*"\n')
        self.wrapper = os.path.join(self.tmp, "wrap.sh")
        with open(self.wrapper, "w") as fh:
            fh.write('#!/bin/sh\nsleep 1.2\nexec "$@"\n')
        for f in (os.path.join(bindir, "lake"), self.wrapper):
            os.chmod(f, 0o755)
        self.env = mock.patch.dict(os.environ, {"PATH": bindir + os.pathsep + os.environ.get("PATH", ""),
                                                "LEAN_SYSROOT": self.tmp})
        self.env.start()
        self.addCleanup(self.env.stop)
        self.pol = mock.patch.object(checkpy.sandbox, "policy",
                                     return_value=mock.Mock(active=False, unsandboxed=lambda *a: None))
        self.pol.start()
        self.addCleanup(self.pol.stop)

    def test_the_untimed_build_excludes_the_wait(self):
        lean = checkpy.Lean(self.tmp, [self.wrapper])
        rc, out, el = lean.run(["build", "SvGolf"], lake_env=False)
        self.assertEqual(rc, 0, out)
        self.assertIn("lake build SvGolf", out)
        self.assertNotIn("SVGOLF_ELAPSED", out)
        self.assertLess(el, 1.0)                     # the build alone, not the 1.2 s in the wrapper
        rec = {"exit": rc, "seconds": el}
        checkpy.note_wait(rec, lean)
        self.assertGreaterEqual(rec["waited"], 1.1)
        self.assertEqual(lean.take_wait(), 0.0)      # taken

    def test_no_wrapper_no_waited(self):
        lean = checkpy.Lean(self.tmp, [])
        rc, out, el = lean.run(["build", "SvGolf"], lake_env=False)
        self.assertEqual(rc, 0, out)
        rec = {"exit": rc, "seconds": el}
        checkpy.note_wait(rec, lean)
        self.assertNotIn("waited", rec)

    def test_a_runner_without_wait_tracking_adds_nothing(self):
        rec = {"exit": 0}
        checkpy.note_wait(rec, object())
        self.assertEqual(rec, {"exit": 0})

    def fake_lean(self, body):
        """A `lean` on PATH (the fake `lake env` execs it): Python, so it buffers its stdout as C stdio does (whole
        blocks into a pipe, line by line into a terminal), the way Lean's own messages are buffered."""
        path = os.path.join(self.tmp, "bin", "lean")
        with open(path, "w") as fh:
            fh.write(f"#!{sys.executable}\nimport sys, time\n" + body)
        os.chmod(path, 0o755)

    def test_a_compile_stopped_at_its_limit_says_which_declaration_finished_last(self):
        """Item 9 of the from-scratch study: the solution's compile (`progress=True`) passes the trace option, gets a
        pseudo-terminal from the supervisor, so lines printed before the kill arrive (through a pipe they would not),
        and `progress` dates them from the command's start, the 1.2 s in the wrapper excluded."""
        self.fake_lean("print(' '.join(sys.argv[1:]))\n"
                       "print('[Kernel] \u2705\ufe0f typechecking declarations [Submission.a]')\n"
                       "time.sleep(0.6)\n"
                       "print('[Kernel] \u2705\ufe0f typechecking declarations [Submission.b]')\n"
                       "time.sleep(60)\n")
        lean = checkpy.Lean(self.tmp, [self.wrapper])
        sol = os.path.join(self.tmp, "Submission", "Solution.lean")
        rc, out, el = lean.compile(sol, timeout=3, progress=True)
        self.assertEqual(rc, 124)
        self.assertIn(checkpy.PROGRESS_OPTION, out)                 # the option reached Lean
        self.assertIn("typechecking declarations [Submission.b]", out)
        self.assertEqual(el, 3.0)                                    # the run took the limit, the wait apart
        self.assertGreaterEqual(lean.take_wait(), 1.1)
        pr = lean.progress
        self.assertEqual((pr["finished"], pr["run_s"], pr["last"]["decls"]), (2, 3.0, "Submission.b"))
        self.assertLess(pr["last"]["at_s"], 1.3)                     # 0.6 s and start-up, not 1.8 s with the wait
        self.assertGreater(pr["last"]["at_s"], 0.5)
        self.assertEqual(checkpy.strip_progress(out).count("[Kernel]"), 0)

    def test_a_compile_that_computes_is_stopped_at_its_cpu_limit(self):
        """The solution's limit counts CPU seconds (decided 2026-11-05): a compile that computes is stopped at its CPU
        limit, long before the wall-clock backstop; `usage` has both readings and names the limit; the progress lines
        are dated in wall seconds from the command's start."""
        self.fake_lean("print('[Kernel] \u2705\ufe0f typechecking declarations [Submission.a]')\n"
                       "while True: pass\n")
        lean = checkpy.Lean(self.tmp, [])
        sol = os.path.join(self.tmp, "Submission", "Solution.lean")
        rc, out, el = lean.compile(sol, timeout=60, cpu_limit=1.5, progress=True)
        self.assertEqual(rc, 124)
        self.assertEqual(lean.usage["stopped_by"], "cpu")
        self.assertGreaterEqual(lean.usage["cpu_s"], 1.5)
        self.assertLess(el, 30)
        self.assertEqual(lean.progress["last"]["decls"], "Submission.a")
        self.assertEqual(lean.progress["run_s"], el)

    def test_a_compile_that_sleeps_meets_the_wall_clock_backstop(self):
        self.fake_lean("time.sleep(60)\n")
        lean = checkpy.Lean(self.tmp, [])
        rc, out, el = lean.compile(os.path.join(self.tmp, "Submission", "Solution.lean"), timeout=2, cpu_limit=1.5)
        self.assertEqual((rc, el, lean.usage["stopped_by"]), (124, 2.0, "wall"))
        self.assertLess(lean.usage["cpu_s"], 1.0)

    def fake_tool(self, name, body):
        """A `name` on PATH (the fake `lake env` execs it): Python."""
        path = os.path.join(self.tmp, "bin", name)
        with open(path, "w") as fh:
            fh.write(f"#!{sys.executable}\nimport sys, time\n" + body)
        os.chmod(path, 0o755)

    # the replay's runs as check.py starts them: the comparator (`lean --run`) and `leanchecker`
    REPLAYS = (("lean", ["lean", "--run", "Comparator.lean", "--goal", "Submission.Goal"], "the comparator"),
               ("leanchecker", ["leanchecker", "Submission.Design", "Submission.Solution"], "leanchecker"))

    def test_a_replay_that_computes_is_stopped_at_its_cpu_limit(self):
        """The comparator and `leanchecker` count CPU seconds (since 2026-11-06; `verify_time_limit_s`): a run that
        computes is stopped at its CPU limit, long before the wall-clock backstop, and the record and the rejection say
        so. The burner: a loop."""
        cpu, wall = checkpy.verify_limits(1.5)
        self.assertEqual(wall, 7.5)                              # VERIFY_WALL_FACTOR x the limit
        for tool, args, who in self.REPLAYS:
            with self.subTest(tool=tool):
                self.fake_tool(tool, "while True: pass\n")
                lean = checkpy.Lean(self.tmp, [])
                rc, out, el = lean.run(args, timeout=wall, cpu_limit=cpu)
                rec = checkpy.verify_record(rc, el, cpu, wall, lean.usage)
                self.assertEqual((rc, rec["stopped_by"], rec["time_limit_counts"]), (124, "cpu", "cpu"))
                self.assertGreaterEqual(rec["cpu_seconds"], 1.5)
                self.assertLess(el, 5.0)
                self.assertTrue(checkpy.solution_timeout_text(cpu, wall, el, rec["cpu_seconds"], rec["stopped_by"],
                                                              who=who).startswith(f"the 1.5 s CPU limit: {who} used "))

    def test_a_replay_that_sleeps_meets_the_wall_clock_backstop(self):
        """A run that waits uses no CPU: the backstop (5 x 0.5 s here) stops it, with its few CPU seconds reported. The
        sleeper: `time.sleep`."""
        cpu, wall = checkpy.verify_limits(0.5)
        for tool, args, who in self.REPLAYS:
            with self.subTest(tool=tool):
                self.fake_tool(tool, "time.sleep(60)\n")
                lean = checkpy.Lean(self.tmp, [])
                rc, out, el = lean.run(args, timeout=wall, cpu_limit=cpu)
                rec = checkpy.verify_record(rc, el, cpu, wall, lean.usage)
                self.assertEqual((rc, el, rec["stopped_by"]), (124, 2.5, "wall"))
                self.assertLess(rec["cpu_seconds"], 0.5)
                self.assertIn(f"the 2.5 s wall-clock backstop: {who} used ",
                              checkpy.solution_timeout_text(cpu, wall, el, rec["cpu_seconds"], rec["stopped_by"], who=who))

    def test_without_progress_the_stopped_compile_loses_its_buffered_lines(self):
        """The control: the same compile without `progress` (a pipe, no option) delivers nothing it printed."""
        self.fake_lean("print('[Kernel] \u2705\ufe0f typechecking declarations [Submission.a]')\n"
                       "time.sleep(60)\n")
        lean = checkpy.Lean(self.tmp, [])
        rc, out, el = lean.compile(os.path.join(self.tmp, "Submission", "Solution.lean"), timeout=2)
        self.assertEqual(rc, 124)
        self.assertNotIn("Submission.a", out)
        self.assertIsNone(lean.progress)


class SolutionTime(unittest.TestCase):
    """Item 17: the solution stage's time against the task's limit, and a warning over half of it. The limit counts the
    CPU seconds of the Lean process tree (decided 2026-11-05); the wall clock is reported apart, and a compile that waits
    instead of computing meets the wall-clock backstop."""

    def lines(self, *a):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            checkpy.log_solution_time(*a)
        return err.getvalue().splitlines()

    def test_under_half(self):
        (ln,) = self.lines(29.5, 300, None, 0, None, 37.2)
        self.assertEqual(ln, "solution: Lean used 37.2 CPU s of the task's 300 s CPU limit (12%), in 29.5 s of wall "
                             "clock")

    def test_over_half_warns_and_the_wait_is_apart(self):
        ln, warn = self.lines(82.4, 300, 300.25, 1, None, 189.7)
        self.assertIn("189.7 CPU s of the task's 300 s CPU limit (63%), in 82.4 s of wall clock; it waited 300.2 s for "
                      "the Lean wrapper first, not counted", ln)
        self.assertTrue(warn.startswith("solution: WARNING: the proof used over half of the 300 s CPU limit"), warn)

    def test_the_warning_reads_cpu_not_wall(self):
        """A loaded machine stretches the wall clock, not the CPU time: 100 s of wall clock for 20 CPU s is no warning."""
        (ln,) = self.lines(100.0, 300, None, 0, None, 20.0)
        self.assertIn("20.0 CPU s of the task's 300 s CPU limit (7%), in 100.0 s of wall clock", ln)

    def test_unmeasured_cpu_says_so(self):
        (ln,) = self.lines(27.0, 300, None, 0)
        self.assertEqual(ln, "solution: Lean ran 27.0 s of wall clock; its CPU time was not measured (the task's "
                             "limit: 300 CPU s)")

    def test_timeout_at_the_cpu_limit(self):
        self.assertEqual(self.lines(131.0, 300, None, 124, None, 300.3, 1500, "cpu"),
                         ["solution: did not finish within the 300 s CPU limit: Lean used 300.3 CPU s in 131.0 s of wall "
                          "clock and was stopped"])

    def test_timeout_at_the_wall_clock_backstop(self):
        self.assertEqual(self.lines(1500.0, 300, None, 124, None, 2.4, 1500, "wall"),
                         ["solution: did not finish within the 1500 s wall-clock backstop: Lean used 2.4 CPU s of its "
                          "300 s CPU limit in 1500.0 s and was stopped, so it waited (a `sleep`, blocked I/O, a machine "
                          "too loaded to run it)"])

    PROGRESS = {"finished": 41, "auxiliary": 7, "run_s": 20.0,
                "last": {"decls": "Submission.band_interface", "at_s": 1.9},
                "slowest": [{"decls": "Submission.band_comb", "s": 0.6}, {"decls": "Submission.a", "s": 0.5, "first": True},
                            {"decls": "Submission.x", "s": 0.01}]}

    def test_timeout_says_where_the_time_went(self):
        stop, where, slow = self.lines(20.0, 20, 31.0, 124, self.PROGRESS, 20.4, 100, "cpu")
        self.assertEqual(stop, "solution: did not finish within the 20 s CPU limit: Lean used 20.4 CPU s in 20.0 s of "
                               "wall clock and was stopped; it waited 31.0 s for the Lean wrapper first, not counted")
        self.assertEqual(where, "solution: where the time went: 41 declarations finished (and 7 auxiliary ones), "
                                "the last `Submission.band_interface` 1.9 s into the run; the 18.1 s after it went to "
                                "what follows it in the file, which had not finished")
        self.assertEqual(slow, "solution: the longest waits for a declaration that finished: "
                               "`Submission.band_comb` 0.6 s, `Submission.a` 0.5 s (the imports included)")

    def test_timeout_before_any_declaration(self):
        stop, where = self.lines(20.0, 20, None, 124, {"finished": 0, "auxiliary": 0, "run_s": 20.0, "last": None,
                                                        "slowest": []})
        self.assertEqual(where, "solution: where the time went: no declaration finished in the 20.0 s: they went to "
                                "the imports and to the first declaration of the file")
        stop, where = self.lines(20.0, 20, None, 124, {"finished": 0, "auxiliary": 2, "run_s": 20.0,
                                                        "last": {"decls": "_tmp._hyg.3", "at_s": 4.0}, "slowest": []})
        self.assertIn("no declaration finished in the 20.0 s (2 auxiliary ones did): they went to", where)

    def test_the_warning_names_the_slowest(self):
        ln, warn = self.lines(75.9, 120, None, 0, self.PROGRESS, 75.9)
        self.assertTrue(warn.endswith("make it faster (the longest waits for a declaration: `Submission.band_comb` "
                                      "0.6 s, `Submission.a` 0.5 s (the imports included))"), warn)


class Progress(unittest.TestCase):
    """Item 9 of the from-scratch study: the progress lines of the solution's compile (`trace.Kernel`), read with the
    time each arrived."""
    LINE = "[Kernel] \u2705\ufe0f typechecking declarations [{}]\n"

    def stamps(self, rows, end):
        """`run_stamped`'s stamps: progress lines at the given times, then the supervisor's control line."""
        return [(t, "out", self.LINE.format(d)) for t, d in rows] + [end]

    def test_times_count_from_the_command_start(self):
        # the call began 5 s before the command (a wrapper's queue): the timeout line arrives at 5 + 20
        st = self.stamps([(5.4, "Submission.a"), (6.0, "Submission.b"), (18.0, "Submission.c")],
                         (25.02, "err", "SVGOLF_TIMEOUT after 20s\n"))
        pr = checkpy.progress_summary(st, 124, 20)
        self.assertEqual((pr["finished"], pr["auxiliary"], pr["run_s"]), (3, 0, 20.0))
        self.assertEqual(pr["last"], {"decls": "Submission.c", "at_s": 12.98})
        self.assertEqual(pr["slowest"], [{"decls": "Submission.c", "s": 12.0}, {"decls": "Submission.b", "s": 0.6},
                                         {"decls": "Submission.a", "s": 0.38, "first": True}])
        self.assertIn("3 declarations finished, the last `Submission.c` 13.0 s into the run; the 7.0 s after it",
                      checkpy.progress_sentence(pr))

    def test_an_auxiliary_line_belongs_to_the_declaration_after_it(self):
        """A tactic's temporary definitions and abstracted proofs are checked while the declaration they serve is
        elaborated, and printed before it: their waits are that declaration's (measured: the tutorial's tactic proof
        prints 340 lines, and its two longest waits, 6.5 s and 0.4 s, ended on `_tmp._@...` lines)."""
        tmp = "_private.Submission.Solution.0._tmp._@.Submission.Solution.4083490425._hygCtx._hyg.35"
        st = self.stamps([(0.5, "Submission.a"), (6.0, tmp), (6.1, "Submission.b._proof_1"), (6.3, "Submission.b"),
                          (9.0, tmp)], (12.0, "err", "SVGOLF_TIMEOUT after 12s\n"))
        pr = checkpy.progress_summary(st, 124, 12)
        self.assertEqual((pr["finished"], pr["auxiliary"]), (2, 3))
        self.assertEqual(pr["slowest"][0], {"decls": "Submission.b", "s": 5.8})
        self.assertEqual(pr["last"], {"decls": "Submission.b", "at_s": 6.3})
        only_aux = checkpy.progress_summary(self.stamps([(2.0, tmp)], (5.0, "err", "SVGOLF_TIMEOUT after 5s\n")), 124, 5)
        self.assertEqual((only_aux["finished"], only_aux["last"]["decls"]), (0, tmp))
        self.assertEqual(checkpy.decl_name(tmp), "an auxiliary declaration")

    def test_a_run_stopped_at_its_cpu_limit_is_anchored_on_its_own_wall_seconds(self):
        """A CPU stop comes before the wall-clock backstop: the run took the wall seconds its timeout line reports
        (9.5 s here), not the backstop (100 s)."""
        st = self.stamps([(5.4, "Submission.a"), (8.0, "Submission.b")],
                         (14.5, "err", "SVGOLF_TIMEOUT after 9.50s cpu_s=20.10 by=cpu\n"))
        pr = checkpy.progress_summary(st, 124, 100)
        self.assertEqual((pr["run_s"], pr["last"]), (9.5, {"decls": "Submission.b", "at_s": 3.0}))

    def test_a_finished_run_is_anchored_on_its_elapsed_line(self):
        st = self.stamps([(1.5, "Submission.a")], (3.0, "err", "SVGOLF_ELAPSED 2.00 peak_rss_mb=1 out_bytes=9 "
                                                               "verdict=none\n"))
        pr = checkpy.progress_summary(st, 0, 120)
        self.assertEqual((pr["run_s"], pr["last"]["at_s"], pr["slowest"]),
                         (2.0, 0.5, [{"decls": "Submission.a", "s": 0.5, "first": True}]))

    def test_no_control_line_no_summary(self):
        self.assertIsNone(checkpy.progress_summary(self.stamps([(1.0, "a")], (1.0, "out", "x\n")), 1, 10))

    def test_the_lines_are_stripped_and_a_leak_is_seen(self):
        out = "x.lean:1:0: warning: w\n" + self.LINE.format("Submission.a") + self.LINE.format("b, c") + "end\n"
        self.assertEqual(checkpy.strip_progress(out), "x.lean:1:0: warning: w\nend\n")
        self.assertFalse(checkpy.progress_leaked(out))
        leak = "x.lean:3:0: error: \u274c\ufe0f Docstring on `#guard_msgs` does not match generated message:\n\n" \
               "trace: " + self.LINE.format("Submission.a")
        self.assertTrue(checkpy.progress_leaked(leak))

    def test_decl_names(self):
        self.assertEqual(checkpy.decl_name("Submission.solution"), "`Submission.solution`")
        self.assertEqual(checkpy.decl_name("_private.Submission.Solution.0.Submission.h"), "`Submission.h`")
        self.assertEqual(checkpy.decl_name("Submission.a, Submission.b"), "`Submission.a` (with `Submission.b`)")
        self.assertEqual(checkpy.decl_name("Submission.f.match_1"), "`Submission.f.match_1`")
        self.assertEqual(checkpy.decl_name("Submission.f._proof_2"), "`Submission.f._proof_2` (an auxiliary of `Submission.f`)")

    def test_run_stamped_is_subprocess_run_with_times(self):
        code = "import sys, time; print('a', flush=True); time.sleep(0.5); print('b'); print('e', file=sys.stderr)"
        proc, st = checkpy.run_stamped([sys.executable, "-c", code], None, None)
        self.assertEqual((proc.returncode, proc.stdout, proc.stderr), (0, "a\nb\n", "e\n"))
        (ta, _, a), (tb, _, b) = [x for x in st if x[1] == "out"]
        self.assertEqual((a, b), ("a\n", "b\n"))
        self.assertGreater(tb - ta, 0.4)


class RankedHeadline(unittest.TestCase):
    """Item 5b: the LAST stderr line of a run that reached `ppa` is the ranked number, area x time, against par."""
    BLOCK = {"available": True, "area_um2_sky130": 460.4416, "area_e4um2_sky130": 4604416, "delay_ps_sky130": 2611}
    PAR = {"name": "add_n", "um2ns": 1202.2130176}

    def res(self, block, score=None):
        return {"task": "add", "stages": {"ppa": {"mode": "auto"}}, "ppa": block, "score": score or {}}

    def test_weighed(self):
        with mock.patch.object(checkpy, "task_par", return_value=(self.PAR, None)):
            self.assertEqual(checkpy.ranked_headline(self.res(self.BLOCK)),
                             "ranked (sky130 A0'): 460.4416 um^2 x 2611 ps = 1202.21 um2*ns; par 1202.21 (add_n)")
        with mock.patch.object(checkpy, "task_par", return_value=(None, None)), \
                mock.patch.object(checkpy, "par_elsewhere", return_value=[]):
            self.assertTrue(checkpy.ranked_headline(self.res(self.BLOCK)).endswith("; par: none recorded"))
        with mock.patch.object(checkpy, "task_par", return_value=(None, "ValueError: x")), \
                mock.patch.object(checkpy, "par_elsewhere", side_effect=AssertionError("not asked")):
            self.assertTrue(checkpy.ranked_headline(self.res(self.BLOCK)).endswith("; par: unavailable (ValueError: x)"))

    def test_no_par_here_but_under_another_build(self):
        """No par under this machine's flow, while the reference records are par under another one (`par_elsewhere`):
        the line says so and points at the rating build, instead of "none recorded"."""
        with mock.patch.object(checkpy, "task_par", return_value=(None, None)), \
                mock.patch.object(checkpy, "par_elsewhere", return_value=["yosys"]):
            self.assertTrue(checkpy.ranked_headline(self.res(self.BLOCK)).endswith(
                "; par: none under this Yosys build, the reference records were weighed under another (README.md, "
                "\"The build ratings use\")"))
        with mock.patch.object(checkpy, "task_par", return_value=(None, None)), \
                mock.patch.object(checkpy, "par_elsewhere", return_value=["script_sha256", "yosys"]):
            self.assertIn("; par: none under this flow (script_sha256, yosys differ), the reference records were "
                          "weighed under another", checkpy.ranked_headline(self.res(self.BLOCK)))

    def test_clocked_time_is_cycles_times_period(self):
        """A clocked run shows the ranked time as its two factors, the latency in cycles and the period (decided
        2026-11-11); a seq- or react-family run, one cycle."""
        block = dict(self.BLOCK, delay_ps_sky130=1000)
        with mock.patch.object(checkpy, "task_par", return_value=(None, None)), \
                mock.patch.object(checkpy, "par_elsewhere", return_value=[]):
            line = checkpy.ranked_headline(self.res(block, {"time_ps": 4000, "cycles": 4, "period_ps": 1000}))
            self.assertTrue(line.startswith("ranked (sky130 A0'): 460.4416 um^2 x 4 cycles x 1000 ps = 1841.77 um2*ns"),
                            line)
            one = checkpy.ranked_headline(self.res(block, {"time_ps": 1000, "cycles": 1, "period_ps": 1000}))
            self.assertTrue(one.startswith("ranked (sky130 A0'): 460.4416 um^2 x 1 cycle x 1000 ps = 460.44 um2*ns"),
                            one)

    def test_liberty_missing_and_not_computed(self):
        off = {"available": False, "reason": "liberty not found: /x\n  fetch it"}
        with mock.patch.object(checkpy, "liberty_problem", return_value="liberty not found: /x"):
            self.assertEqual(checkpy.ranked_headline(self.res(off)),
                             "ranked: liberty missing, run python3.12 score/ppa.py --fetch-liberty")
        with mock.patch.object(checkpy, "liberty_problem", return_value=None):
            self.assertEqual(checkpy.ranked_headline(self.res({"available": False, "reason": "a cell\n outside"})),
                             "ranked: not computed: a cell outside")
        illegal = {"available": False, "illegal": True, "reason": "the net n is illegal"}
        with mock.patch.object(checkpy, "liberty_problem", side_effect=AssertionError("not asked")):
            self.assertEqual(checkpy.ranked_headline(self.res(illegal)), "ranked: not computed: the net n is illegal")

    def test_a_run_that_did_not_reach_ppa_has_none(self):
        self.assertIsNone(checkpy.ranked_headline({"stages": {"design": {}}, "ppa": self.BLOCK}))

    def test_the_real_par_of_add_is_its_board_s(self):
        """`task_par` reads leaderboard.py's `par_now` (the shipped reference records)."""
        par, why = checkpy.task_par("add")
        self.assertIsNone(why)
        if par is not None:             # (None when this machine's Yosys is not the records' flow)
            self.assertEqual(par["name"], "add_n")
            self.assertEqual(checkpy.par_elsewhere("add"), [])       # par here: the record's flow is this one
        else:                           # another flow: the reference records still name one, and it differs
            self.assertNotEqual(checkpy.par_elsewhere("add"), [])
        self.assertEqual(checkpy.par_elsewhere("no_such_task"), [])  # advice: never an exception


class ToolMessages(unittest.TestCase):
    """The post-synthesis stage's infrastructure errors say what went wrong with the toolchain: Verilator's own stderr
    when it fails to start (a Perl module its scrubbed environment hides), where the compiler's name came from ($CXX),
    and the library the dynamic loader did not find when the compiled model cannot start (an infrastructure error,
    never a rejection: the model's main() never ran)."""

    def fake(self, tmp, name, body):
        p = os.path.join(tmp, name)
        with open(p, "w") as fh:
            fh.write("#!/bin/sh\n" + body)
        os.chmod(p, 0o755)
        return p

    def test_verilator_says_why_it_failed(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.fake(tmp, "verilator", "echo \"Can't locate X.pm in @INC (you may need to install the X module)\" >&2\n"
                      "exit 2\n")
            with mock.patch.dict(os.environ, {"PATH": tmp + os.pathsep + os.environ.get("PATH", "")}):
                with self.assertRaises(postsynth.InfraError) as cm:
                    postsynth.verilator_info()
        msg = str(cm.exception)
        self.assertIn("(exit 2)", msg)
        self.assertIn("Can't locate X.pm in @INC", msg)
        self.assertIn("the tools run with an allowlisted environment: README.md, \"Sandbox\"", msg)

    def test_the_compiler_named_by_cxx(self):
        with mock.patch.dict(os.environ, {"CXX": "no-such-compiler-svgolf"}):
            with self.assertRaises(postsynth.InfraError) as cm:
                postsynth.cxx_path()
        self.assertIn("`no-such-compiler-svgolf` is not on PATH", str(cm.exception))
        self.assertIn("is the value of $CXX: set CXX to a compiler on PATH, or unset it to use `c++`", str(cm.exception))
        env = {k: v for k, v in os.environ.items() if k != "CXX"}
        with mock.patch.dict(os.environ, env, clear=True), mock.patch.object(postsynth.shutil, "which",
                                                                             return_value=None):
            with self.assertRaises(postsynth.InfraError) as cm:
                postsynth.cxx_path()
        self.assertIn("`c++` is not on PATH", str(cm.exception))
        self.assertNotIn("$CXX", str(cm.exception))

    def test_a_model_the_loader_cannot_start_is_infrastructure(self):
        off = postsynth.sandbox.Policy("off")          # (another test of this process may have left one installed)
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(postsynth.sandbox, "policy", return_value=off):
            exe = self.fake(tmp, "VNET", "echo \"$0: error while loading shared libraries: libatomic.so.1: cannot open "
                            "shared object file: No such file or directory\" >&2\nexit 127\n")
            with self.assertRaises(postsynth.InfraError) as cm:
                postsynth.vl_run(exe, [("a", 1)], [("y", 1)], [{"a": 0}], tmp, "t", 60)
            self.assertIn("the dynamic loader did not find `libatomic.so.1`", str(cm.exception))
            self.assertIn("the toolchain, not the design", str(cm.exception))
            # a model that ran and printed malformed rows is the design's (a rejection by the caller), as before
            bad = self.fake(tmp, "BAD", "echo 1 0\necho oops >&2\nexit 3\n")
            rows, _, err = postsynth.vl_run(bad, [("a", 1)], [("y", 1)], [{"a": 0}], tmp, "u", 60)
            self.assertIsNone(rows)
            self.assertIn("(exit 3, end marker", err)
        # macOS's dyld, and the cases that are not the loader's
        done = postsynth.subprocess.CompletedProcess
        with self.assertRaises(postsynth.InfraError) as cm:
            postsynth.loader_failure(done([], -6, "", "dyld[123]: Library not loaded: @rpath/libc++.1.dylib\n"))
        self.assertIn("`@rpath/libc++.1.dylib`", str(cm.exception))
        postsynth.loader_failure(done([], 0, "", "error while loading shared libraries: x.so: ..."))
        postsynth.loader_failure(done([], 127, "0 1\n", "error while loading shared libraries: x.so: ..."))
        postsynth.loader_failure(done([], 1, "", "some other failure"))


class StageDir(unittest.TestCase):
    """`--stage-dir DIR` replaces an existing DIR only when it is empty or holds check.py's own `.svgolf-stage` file:
    a directory check.py did not make is refused with exit status 2 and left as it was."""

    def test_the_rule(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertIsNone(checkpy.stage_dir_problem(os.path.join(tmp, "new")))
            empty = os.path.join(tmp, "empty")
            os.makedirs(empty)
            self.assertIsNone(checkpy.stage_dir_problem(empty))
            made = os.path.join(tmp, "made")
            os.makedirs(made)
            for name in (checkpy.STAGE_MARK, "Submission"):
                with open(os.path.join(made, name), "w") as fh:
                    fh.write("x")
            self.assertIsNone(checkpy.stage_dir_problem(made))
            other = os.path.join(tmp, "other")
            os.makedirs(other)
            with open(os.path.join(other, "notes.txt"), "w") as fh:
                fh.write("mine")
            self.assertIn("was not made by check.py (no .svgolf-stage in it)", checkpy.stage_dir_problem(other))
            self.assertIn("is not a directory", checkpy.stage_dir_problem(os.path.join(other, "notes.txt")))
            link = os.path.join(tmp, "link")
            os.symlink(made, link)                  # a link to a directory check.py made: still refused, as a link
            self.assertIn("is a symbolic link", checkpy.stage_dir_problem(link))

    def test_check_py_refuses_and_deletes_nothing(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, "notes.txt"), "w") as fh:
                fh.write("mine")
            p = subprocess.run([sys.executable, os.path.join(SVGOLF, "check.py"), os.path.join(TASKS, "_example"),
                                os.path.join(TASKS, "_example", "reference", "band.sv"), "--unproved",
                                "--stage-dir", tmp], capture_output=True, text=True, timeout=120,
                               env=dict(os.environ, SVGOLF_LEAN_WRAP="", SVGOLF_SANDBOX="off"))
            self.assertEqual(p.returncode, 2, p.stderr)
            self.assertIn("was not made by check.py", p.stderr)
            self.assertEqual(os.listdir(tmp), ["notes.txt"])


class MainExitAndHeadline(unittest.TestCase):
    """Item 5a: a clean `--unproved` run exits 0 (its sentence a note, `unproved_ok`); a failed stage exits 1; the
    ranked headline is the last stderr line."""
    ARGV = [os.path.join(SVGOLF, "tasks", "_example"),
            os.path.join(SVGOLF, "tests", "_example", "attacks", "z_rare.sv"), "--unproved"]

    def run_main(self, result, headline=None):
        out, err = io.StringIO(), io.StringIO()
        env = {k: v for k, v in os.environ.items() if not k.startswith("SVGOLF_LEAN_WRAP")}
        with mock.patch.object(checkpy, "check", lambda *a, **kw: result), \
                mock.patch.object(checkpy, "ranked_headline", lambda res: headline), \
                mock.patch.dict(os.environ, env, clear=True), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = checkpy.main(self.ARGV + ["--sandbox", "off"])
        return rc, json.loads(out.getvalue()), err.getvalue().splitlines()

    def test_clean_unproved_exits_zero(self):
        rc, res, _ = self.run_main({"accepted": False, "stage": "unproved", "errors": [], "notes": ["ok"],
                                    "unproved_ok": True, "stages": {}})
        self.assertEqual((rc, res["unproved_ok"], res["accepted"]), (0, True, False))

    def test_a_failed_stage_exits_one(self):
        rc, _, _ = self.run_main({"accepted": False, "stage": "fourstate", "errors": ["x"], "stages": {}})
        self.assertEqual(rc, 1)

    def test_the_headline_is_the_last_stderr_line(self):
        rc, _, err = self.run_main({"accepted": False, "stage": "unproved", "errors": [], "notes": ["ok"],
                                    "unproved_ok": True, "stages": {}, "warnings": ["functional: a warning"]},
                                   headline="ranked (sky130 A0'): 1 um^2 x 2 ps = 0.00 um2*ns; par: none recorded")
        self.assertEqual(err[-2:], ["functional: a warning",
                                    "ranked (sky130 A0'): 1 um^2 x 2 ps = 0.00 um2*ns; par: none recorded"])

    def test_not_a_task_directory_is_a_usage_error(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as cm:
            checkpy.main([os.path.join(SVGOLF, "tasks"), self.ARGV[1], "--unproved"])
        self.assertEqual(cm.exception.code, 2)
        self.assertIn("is not a task directory (it has no task.json)", err.getvalue())


class StageLines(unittest.TestCase):
    def test_format(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            checkpy.stage_start("design", "compiling it")
            checkpy.stage_start("solution", "limit 300 s", ["/w/slot.sh"])
            checkpy.stage_start("extract")
        self.assertEqual(err.getvalue().splitlines(),
                         ["check: design ... (compiling it)",
                          "check: solution ... (limit 300 s; behind the Lean wrapper, which may queue it first)",
                          "check: extract ..."])


if __name__ == "__main__":
    unittest.main(verbosity=1)
