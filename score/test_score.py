#!/usr/bin/env python3.12
"""Tests for score.py: known gate counts, determinism (two runs, identical
JSON), the GE arithmetic, an unpriced cell, the Pareto filter, the source
gate in front of Yosys, the canonical layout (two-stage flow) and the written
netlist.

    python3.12 score/test_score.py
"""
import json
import math
import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import score  # noqa: E402

BAND = os.path.join(SVGOLF, "tasks", "_example", "reference", "band.sv")
CNT = os.path.join(SVGOLF, "tests", "seq_counter", "reference", "cnt.sv")
RIPPLE = os.path.join(HERE, "tests", "ok_constant.sv")
GATE = os.path.join(HERE, "tests", "gate")


class ScoreTest(unittest.TestCase):
    def test_band_known(self):
        r = score.score([BAND], "band", {"N": 16})
        self.assertEqual(r["gates"], {"AND": 16})
        self.assertEqual(r["area_mge"], 16 * 1333)
        self.assertEqual(r["area_ge"], 21.328)
        self.assertEqual(r["depth"], 1)

    def test_parameter_override_changes_size(self):
        r4 = score.score([BAND], "band", {"N": 4})
        self.assertEqual(r4["gates"], {"AND": 4})

    def test_deterministic_cli(self):
        """Two separate CLI runs give byte-identical JSON."""
        cmd = [sys.executable, os.path.join(HERE, "score.py"), RIPPLE, "--top", "ok_constant",
               "--param", "N=16"]
        a = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        b = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        self.assertEqual(a, b)
        r = json.loads(a)
        self.assertGreater(r["num_gates"], 16)
        self.assertEqual(r["area_mge"], sum(score.load_ge_table()[g] * n
                                            for g, n in r["gates"].items()))

    def test_repeat_flag(self):
        r = score.score([RIPPLE], "ok_constant", {"N": 8}, repeat=2)
        self.assertEqual(r["repeat_identical"], 2)

    def test_flipflop_is_unpriced(self):
        path = os.path.join(HERE, "tests", "reg.sv")
        with self.assertRaises(score.ScoreError):
            score.score([path], "reg1", {})

    def test_gate_is_load_bearing(self):
        """Without the source gate, Yosys scores `ifdef SYNTHESIS` / `unique
        case` designs as constants (0 GE) although the extractor reads `a & b`;
        with the gate (the default) they are refused."""
        for f in ("ifdef_synth.sv", "ifdef_yosys.sv", "translate_off2.sv", "unique_case.sv",
                  "priority_case.sv"):
            path = os.path.join(GATE, f)
            ungated = score.score([path], "band", {"N": 16}, gate=False)
            self.assertEqual((ungated["area_mge"], ungated["depth"]), (0, 0), f)
            self.assertFalse(ungated["gated"])
            with self.assertRaises(score.ScoreError, msg=f):
                score.score([path], "band", {"N": 16})

    def test_gate_strips_comments(self):
        """Comments of every shape are stripped; the score is that of `a & b`."""
        r = score.score([os.path.join(GATE, "ok_comments.sv")], "band", {"N": 16})
        self.assertEqual(r["gates"], {"AND": 16})
        self.assertTrue(r["gated"])
        self.assertNotEqual(r["sources"][0]["sha256"], r["sources"][0]["canonical_sha256"])

    def test_canonical_layout(self):
        """The two-stage flow scores the canonical RTLIL, which layout does not
        change: leading blank lines, every line joined, re-indentation give a
        byte-identical canonical RTLIL (`rtlil_sha256`) and so the same score.
        (The full battery, renaming and item order included, is the `canon`
        step of tests/run.py.)"""
        import srcgate
        import tempfile
        canon, findings = srcgate.gate_file(RIPPLE)
        self.assertEqual(findings, [])
        lines = [ln.strip() for ln in canon.splitlines() if ln.strip()]
        variants = {"blank": "\n" * 40 + canon, "oneline": " ".join(lines) + "\n",
                    "indent": "\n".join("\t\t" + ln for ln in lines) + "\n"}
        base = score.score([RIPPLE], "ok_constant", {"N": 16})
        with tempfile.TemporaryDirectory() as d:
            for name, text in variants.items():
                path = os.path.join(d, f"{name}.sv")
                with open(path, "w") as fh:
                    fh.write(text)
                r = score.score([path], "ok_constant", {"N": 16})
                self.assertEqual(r["rtlil_sha256"], base["rtlil_sha256"], name)
                self.assertEqual((r["area_mge"], r["depth"], r["gates"]),
                                 (base["area_mge"], base["depth"], base["gates"]), name)

    def test_netlist_and_shas(self):
        """The scored netlist is written on request (after stat/ltp), and the
        result records both pinned scripts' sha256."""
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            net = os.path.join(d, "net.v")
            r = score.score([BAND], "band", {"N": 4}, netlist_out=net)
            with open(net) as fh:
                text = fh.read()
        self.assertIn("module band(", text)
        self.assertEqual(text.count("\\$_AND_ "), 4)
        self.assertEqual(r["script_sha256"], score.sha256_file(score.SCRIPT))
        self.assertEqual(r["canon_script_sha256"], score.sha256_file(score.CANON_SCRIPT))

    def test_pareto(self):
        recs = [{"area_mge": 10, "depth": 5}, {"area_mge": 8, "depth": 7},
                {"area_mge": 12, "depth": 4}, {"area_mge": 11, "depth": 6},
                {"area_mge": 10, "depth": 5}]
        front = score.pareto(recs)
        self.assertEqual([(r["area_mge"], r["depth"]) for r in front],
                         [(8, 7), (10, 5), (10, 5), (12, 4)])


class SeqFlowTest(unittest.TestCase):
    """The clocked flow (`--seq`): svgolf_seq.ys + ge_seq.json."""

    def test_counter_flops_priced(self):
        r = score.score([CNT], "cnt", {"N": 8}, flow="seq")
        self.assertEqual((r["flow"], r["ffs"], r["gates"]["DFF_P"]), ("seq", 8, 8))
        self.assertEqual(r["area_ff_mge"], 8 * score.load_ge_table(score.GE_SEQ)["DFF_P"])
        self.assertEqual(r["area_comb_mge"] + r["area_ff_mge"], r["area_mge"])
        self.assertEqual(r["period"], r["depth"])
        self.assertFalse(r["reg_overhead_included"])

    def test_reg_overhead_flag(self):
        r = score.score([CNT], "cnt", {"N": 8}, flow="seq", reg_overhead=True)
        self.assertEqual(r["period"], r["depth"] + math.ceil(r["reg_overhead_nand2"]))

    def test_comb_flow_unchanged(self):
        """The combinational flow's result has none of the clocked keys and its own hashes."""
        r = score.score([BAND], "band", {"N": 4})
        self.assertFalse({"flow", "ffs", "period"} & set(r))
        self.assertEqual(r["script_sha256"], score.sha256_file(score.SCRIPT))
        self.assertEqual(r["ge_table_sha256"], score.sha256_file(score.GE_TABLE))

    def test_no_fsm_pass(self):
        """The clocked flow's `synth` runs with `-nofsm` (decided 2026-11-06), the combinational flow's without: an
        ordinary reset controller whose state register every reader compares with a constant keeps its own two
        flops (the fsm pass mapped it before); the log pattern `FSM_MAPPED` stays as a backstop."""
        render = lambda path: score.render_script("r.il", "t", "s", "l", "n", path).splitlines()  # noqa: E731
        self.assertIn("synth -flatten -nofsm -top t", render(score.SCRIPT_SEQ))
        self.assertIn("synth -flatten -top t", render(score.SCRIPT))
        sv = os.path.join(SVGOLF, "tests", "seq_counter", "never_loaded", "fsm_reset_controller.sv")
        r = score.score([sv], "cnt", {"N": 8}, flow="seq")
        self.assertEqual((r["ffs"], r["flop_removals"]["fsm_mapped"]), (10, []))
        self.assertEqual(len(score.flop_removals("Mapping FSM `$fsm$\\s$31' from module `\\cnt'.\n")["fsm_mapped"]), 1)

    def test_purge(self):
        """The clocked flow's last clean-up is `opt_clean -purge` (decided 2026-11-07), the combinational flow's plain
        `opt_clean`. The rotating-priority arbiter at N = 8, whose scored netlist kept a partly undriven dead techmap
        wire before (`\\_269_.B`, which the post-synthesis lint refused: tasks/arbiter/README.md, F6), has the gates
        plain `opt_clean` gave (MEASURED 2026-11-07: 310.294 GE, depth 13, 11 flops); that the netlist is now
        lint-clean is tests/checker/test_clocked_post.py's (the post-synthesis check at N = 3, 5, 8)."""
        render = lambda path: score.render_script("r.il", "t", "s", "l", "n", path).splitlines()  # noqa: E731
        self.assertIn("opt_clean -purge", render(score.SCRIPT_SEQ))
        self.assertNotIn("opt_clean -purge", render(score.SCRIPT))
        sv = os.path.join(SVGOLF, "tests", "arbiter", "designs", "rotate.sv")
        r = score.score([sv], "arbiter", {"N": 8}, flow="seq")
        self.assertEqual((r["area_mge"], r["depth"], r["ffs"]), (310294, 13, 11))

    def test_one_flop(self):
        r = score.score([os.path.join(HERE, "tests", "reg.sv")], "reg1", {}, flow="seq")
        self.assertEqual((r["ffs"], r["area_comb_mge"]), (1, 0))

    def test_async_reset_and_init_refused(self):
        for f, top in (("reg_async.sv", "reg_async"), ("reg_init.sv", "reg_init")):
            with self.subTest(f), self.assertRaises(score.ScoreError):
                score.score([os.path.join(HERE, "tests", f)], top, {}, gate=False, flow="seq")

    def test_seq_deterministic_cli(self):
        cmd = [sys.executable, os.path.join(HERE, "score.py"), CNT, "--top", "cnt", "--param", "N=16",
               "--seq"]
        a = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        b = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        self.assertEqual(a, b)

    def test_ge_seq_is_derived(self):
        """ge_seq.json is exactly what derive_seq_prices.py gets from the pinned liberty."""
        cmd = [sys.executable, os.path.join(HERE, "derive_seq_prices.py"), "--check"]
        p = subprocess.run(cmd, capture_output=True, text=True)
        if p.returncode == 2:
            self.skipTest("the pinned liberty is not available (python3.12 score/ppa.py --fetch-liberty)")
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
