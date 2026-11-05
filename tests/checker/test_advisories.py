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

    python3.12 tests/checker/test_advisories.py
"""

import contextlib
import importlib.util
import io
import json
import os
import random
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


if __name__ == "__main__":
    unittest.main(verbosity=1)
