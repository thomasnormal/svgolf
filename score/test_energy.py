#!/usr/bin/env python3.12
"""Tests for energy.py (the sky130 energy columns, on the repaired netlist of sky130_a0_v3): bit-identical runs, the glitch
factor of a reconvergence-free design, leakage as the plain sum, no energy for an illegal netlist, the seed policy (dev
seed fixed, official seeds from the salt), a clocked netlist, and the golden values of tests/expected_sky130.json (every
entry, about 20 s). Skipped without the pinned liberty.

    python3.12 score/test_energy.py
    UPDATE_GOLDEN=1 python3.12 score/test_energy.py      # re-record tests/expected_sky130.json's `energy` block
"""
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import energy  # noqa: E402
import ppa  # noqa: E402
import score  # noqa: E402

UPDATE = os.environ.get("UPDATE_GOLDEN") == "1"
GOLDEN = os.path.join(SVGOLF, "tests", "expected_sky130.json")
# the designs of the energy goldens, `task/stem` -> source; the top is the task's, the point the key's, a clocked fixture
# (`seq/`) goes through the clocked flow, the banned Yosys multiplier past the source gate
GOLDEN_SOURCES = {"add/add_n": "tasks/add/reference/add_n.sv", "add/add_n_kogge_stone": "tests/add/baselines/add_n_kogge_stone.sv",
                  "add/add_n_sklansky": "tests/add/baselines/add_n_sklansky.sv", "add/cmp_carry": "tests/add/baselines/cmp_carry.sv",
                  "clmul/clmul_n": "tasks/clmul/reference/clmul_n.sv", "mul/dadda_rc": "tests/mul/baselines/dadda_rc.sv",
                  "mul/mul_n": "tasks/mul/reference/mul_n.sv",
                  "mul/mul_tree": "tasks/mul/reference/mul_tree.sv", "mul/mul_tree_h": "tasks/mul/reference/mul_tree_h.sv",
                  "mul/mul_wallace": "tasks/mul/reference/mul_wallace.sv", "mul/yosys_mul": "tests/mul/baselines/yosys_mul.sv",
                  "seq/cnt": "tests/seq_counter/reference/cnt.sv"}
GOLDEN_TOPS = {"add": "add_n", "clmul": "clmul_n", "mul": "mul_n", "seq": "cnt"}
GOLDEN_UNGATED = {"mul/yosys_mul"}


def golden_measure(key, fields, lib, pins):
    """The energy of one golden entry (`task/stem@NAME=value`): its fields, measured as recorded."""
    name, point = key.split("@")
    k, v = point.split("=")
    task = name.split("/")[0]
    path = os.path.join(tempfile.mkdtemp(prefix="svgolf-energy-test-"), "n.v")
    score.score([os.path.join(SVGOLF, GOLDEN_SOURCES[name])], GOLDEN_TOPS[task], {k: int(v)}, netlist_out=path,
                flow="seq" if task == "seq" else "comb", gate=name not in GOLDEN_UNGATED)
    with open(path) as fh:
        got = energy.measure(fh.read(), lib, pins)
    return {f: got[f] for f in fields}


REG = "module reg1(clk, d, q);\n  input clk;\n  input d;\n  output q;\n  \\$_DFF_P_ _1_ (.C(clk), .D(d), .Q(q));\nendmodule\n"


def netlist(sv, top, params):
    path = os.path.join(tempfile.mkdtemp(prefix="svgolf-energy-test-"), "n.v")
    score.score([os.path.join(SVGOLF, sv)], top, params, netlist_out=path)
    with open(path) as fh:
        return fh.read()


class EnergyTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        try:
            cls.lib, cls.pins = ppa.open_library()
        except ppa.PpaError as e:
            raise unittest.SkipTest(f"the pinned liberty is not available: {e}")
        cls.band = netlist("tasks/_example/reference/band.sv", "band", {"N": 4})
        cls.add = netlist("tasks/add/reference/add_n.sv", "add_n", {"N": 16})

    def test_bit_identical(self):
        self.assertEqual(energy.measure(self.add, self.lib, self.pins), energy.measure(self.add, self.lib, self.pins))

    def test_glitch_factor(self):
        self.assertEqual(energy.measure(self.band, self.lib, self.pins)["glitch_factor"], 1.0)   # no reconvergence
        self.assertGreater(energy.measure(self.add, self.lib, self.pins)["glitch_factor"], 1.0)  # the ripple glitches

    def test_leakage_is_the_cell_sum(self):
        """Over the cells of the REPAIRED netlist the ranked score weighs (band at N = 4: four and2_1 cells, nothing over a
        limit, so nothing buffered)."""
        hist = ppa.analyze(self.band, self.lib, self.pins).hist
        self.assertEqual(hist, {"and2_1": 4})
        pw = energy.Power(self.lib)
        want = sum(n * pw.cell(self.pins.prefix + c)[0] for c, n in hist.items())
        self.assertAlmostEqual(energy.measure(self.band, self.lib, self.pins)["leakage_sky130_v1"], round(want, 3))

    def test_the_repair_s_buffers_and_tie_cells_are_weighed(self):
        """An input wired to 20 output bits (200 fF on its driver: over a task's buf_1, within the default buf_8) and 300
        constant output bits (two conb_1): the energy is that of the repaired netlist, its buffer and tie cells in the
        leakage, under the input drive it was weighed with."""
        pw = energy.Power(self.lib)
        b1 = self.pins.prefix + "buf_1"
        bc = "module bc(a, y);\n  input a;\n  output [19:0] y;\n  assign y = {" + ", ".join(["a"] * 20) + "};\nendmodule\n"
        for text, drive, cells in ((bc, b1, {"buf_2": 1}), (bc, None, {}),
                                   ("module c(a, y);\n  input a;\n  output [299:0] y;\n  assign y = {299'b0, a};\nendmodule\n",
                                    None, {"conb_1": 2})):
            self.assertEqual(ppa.analyze(text, self.lib, self.pins, input_drive=drive).hist, cells)
            want = sum(n * pw.cell(self.pins.prefix + c)[0] for c, n in cells.items())
            got = energy.measure(text, self.lib, self.pins, input_drive=drive)
            self.assertAlmostEqual(got["leakage_sky130_v1"], round(want, 3))
            self.assertEqual(got["input_drive"], drive or self.pins.input_drive_default)

    def test_an_illegal_netlist_has_no_energy(self):
        """A netlist the ranked score rejects (one the repair cannot make legal; the weighing is patched to say so: no real
        netlist of the pinned flow is known to be one) has no energy either: IllegalNetlist, never a number read off an
        extrapolated table."""
        from unittest import mock
        with mock.patch.object(ppa, "analyze", side_effect=ppa.IllegalNetlist("cannot be made legal")):
            with self.assertRaises(ppa.IllegalNetlist):
                energy.measure(self.band, self.lib, self.pins)

    def test_seed_policy(self):
        a = energy.measure(self.band, self.lib, self.pins, salt="public")
        b = energy.measure(self.band, self.lib, self.pins, salt="secret")
        self.assertEqual(a["per_seed"]["dev"], b["per_seed"]["dev"])
        self.assertNotEqual(set(a["per_seed"]), set(b["per_seed"]))
        self.assertEqual((a["stimulus"]["salted"], b["stimulus"]["salted"]), (False, True))
        self.assertNotIn("secret", json.dumps(b))

    def test_clocked(self):
        r = energy.measure(REG, self.lib, self.pins, cycles=3)
        self.assertEqual((r["flops"], r["clock_tree_buffers"]), (1, 0))
        data = sum(v["data_fj"] for s, v in r["per_seed"].items() if s != "dev") / energy.OFFICIAL
        self.assertAlmostEqual(r["energy_cycle_sky130_v1"], round(data + r["clock_pins_fj"] + r["clock_tree_fj"], 3),
                               places=2)
        self.assertAlmostEqual(r["energy_transaction_sky130_v1"]["fj"], round(3 * r["energy_cycle_sky130_v1"], 3), places=2)

    def test_golden(self):
        """Every entry of tests/expected_sky130.json's `energy` block, measured again (UPDATE_GOLDEN=1: written back, the
        file otherwise unchanged)."""
        with open(GOLDEN) as fh:
            gold = json.load(fh)
        got = energy.measure(self.add, self.lib, self.pins)
        for k, v in gold["energy"]["add/add_n@N=16"].items():
            if not UPDATE:
                self.assertEqual(got[k], v, k)
        new = {key: golden_measure(key, fields, self.lib, self.pins) for key, fields in gold["energy"].items()}
        if UPDATE:
            gold["energy"] = new
            with open(GOLDEN, "w") as fh:
                json.dump(gold, fh, indent=1, sort_keys=True)
                fh.write("\n")
            return
        for key, fields in gold["energy"].items():
            with self.subTest(key=key):
                self.assertEqual(new[key], fields)


if __name__ == "__main__":
    unittest.main(verbosity=2)
