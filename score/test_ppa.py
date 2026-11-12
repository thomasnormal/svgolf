#!/usr/bin/env python3.12
"""Tests for ppa.py (PPA columns): a hand-computed tiny netlist on a synthetic liberty (always runs), the failure
modes (missing or wrong liberty, a cell outside the A0' table, undriven or doubly driven nets, loops, x/z constants, a wrong
pin map or table template), determinism across processes and hash seeds, flow A1' (WP-X4: the mapped netlist weighed by the
same STA, the equivalence sample against the scored netlist, the mapped-flow pins, the loud reasons), and, when the pinned
sky130 liberty is present, the real library: its pins, the ten gate cells against the Yosys gate semantics,
hand-interpolated single-gate delays, the GE ratios of design/ppa/sky130.md, the golden (GE, depth, um^2, ps) of every
reference design through the pinned flow, and the golden A1' columns of every reference and baseline through the real
`abc -liberty` mapping; the repair of sky130_a0_v2 (buffering only: buffer trees and replicated tie cells on every shape the
11/04 review found, balanced and legal by construction, the repaired Verilog read back, simulated and read by Yosys,
byte-identical across processes; what it cannot fix rejected with the net named; the review's 24 RTL probes legal through
the pinned flow); the per-task input drive of sky130_a0_v3 (every allowed cell, the repair's input budget, the task's
`input_drive` through the CLI, an unknown cell a task-configuration error).

    python3.12 score/test_ppa.py

The liberty (12.8 MB) is not in the repository: `python3.12 score/ppa.py --fetch-liberty`, or $SVGOLF_SKY130_LIB. Without it
the real-library tests are SKIPPED; SVGOLF_PPA_REQUIRE_LIB=1 turns that into a failure (use it in release runs).
"""
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import ppa  # noqa: E402
import ppa_validate  # noqa: E402

PREFIX = "sky130_fd_sc_hd__"
BUF1 = PREFIX + "buf_1"      # the weakest allowed input drive (a task may choose it): the repair's shapes are built for it
REAL_PINS = ppa.Pins()
REAL_LIB = ppa.find_liberty(None, REAL_PINS)
HAVE_LIB = os.path.isfile(REAL_LIB)
REQUIRE_LIB = os.environ.get("SVGOLF_PPA_REQUIRE_LIB") == "1"
needs_lib = unittest.skipUnless(HAVE_LIB, f"the pinned sky130 liberty is absent ({REAL_LIB}); run "
                                           "`python3.12 score/ppa.py --fetch-liberty`")


def have_flow():
    import score
    if shutil.which(score.yosys_bin()) is None:
        return False
    try:
        import pyslang  # noqa: F401
    except ImportError:
        return False
    return True


needs_flow = unittest.skipUnless(HAVE_LIB and have_flow(), "needs the pinned liberty, Yosys and pyslang")


# ------------------------------------------------------------------------------------------------ a synthetic liberty
def _tbl(kind, a, b, c):
    """A 2x2 NLDM table of f(s, l) = a + b*s + c*l on s in {0, 0.1} ns, l in {0, 0.02} pF: bilinear interpolation
    reproduces f exactly, so the hand computation below is exact."""
    f = lambda s, l: repr(a + b * s + c * l)
    return (f'        {kind} ("tpl") {{ index_1("0.0, 0.1"); index_2("0.0, 0.02");\n'
            f'          values("{f(0.0, 0.0)}, {f(0.0, 0.02)}", "{f(0.1, 0.0)}, {f(0.1, 0.02)}"); }}\n')


def _arc(related, rise, fall, rtr, ftr, sense="negative_unate"):
    return (f'      timing () {{ related_pin : "{related}"; timing_sense : "{sense}"; timing_type : "combinational";\n'
            + _tbl("cell_rise", *rise) + _tbl("cell_fall", *fall)
            + _tbl("rise_transition", *rtr) + _tbl("fall_transition", *ftr) + "      }\n")


def mini_lib(inv_fn="(!A)", with_nand=True, with_conb=True, cap_unit="pf", var2="total_output_net_capacitance",
             time_unit="1ns", with_buf=True):
    """inv_1 (area 3.75), nand2_1 (5.0), conb_1 (3.75) and buf_1 (3.75, the synthetic pins' default input drive) with
    the tables of the hand computation: cell_rise = a + b*slew + c*load ... (coefficients below)."""
    t = [f'library ("mini") {{\n    time_unit : "{time_unit}";\n    voltage_unit : "1V";\n'
         f'    capacitive_load_unit(1.0000000000, {cap_unit});\n'
         f'    lu_table_template ("tpl") {{ variable_1 : "input_net_transition"; variable_2 : "{var2}";\n'
         f'      index_1("0, 1"); index_2("0, 1"); }}\n']
    t.append(f'    cell ("{PREFIX}inv_1") {{\n      area : 3.7500000000;\n'
             '      pin ("A") { capacitance : 0.002; direction : "input"; }\n'
             f'      pin ("Y") {{ direction : "output"; function : "{inv_fn}";\n'
             + _arc("A", (0.020, 0.5, 5.0), (0.010, 0.4, 4.0), (0.015, 0.3, 10.0), (0.012, 0.2, 8.0))
             + "      }\n    }\n")
    if with_nand:
        t.append(f'    cell ("{PREFIX}nand2_1") {{\n      area : 5.0000000000;\n'
                 '      pin ("A") { capacitance : 0.003; direction : "input"; }\n'
                 '      pin ("B") { capacitance : 0.003; direction : "input"; }\n'
                 '      pin ("Y") { direction : "output"; function : "(!A) | (!B)";\n'
                 + _arc("A", (0.030, 0.6, 6.0), (0.020, 0.5, 5.0), (0.025, 0.3, 7.0), (0.018, 0.25, 6.0))
                 + _arc("B", (0.035, 0.6, 6.0), (0.025, 0.5, 5.0), (0.025, 0.3, 7.0), (0.018, 0.25, 6.0))
                 + "      }\n    }\n")
    if with_conb:
        t.append(f'    cell ("{PREFIX}conb_1") {{\n      area : 3.7500000000;\n'
                 '      pin ("HI") { direction : "output"; function : "1"; }\n'
                 '      pin ("LO") { direction : "output"; function : "0"; }\n    }\n')
    if with_buf:
        t.append(f'    cell ("{PREFIX}buf_1") {{\n      area : 3.7500000000;\n'
                 '      pin ("A") { capacitance : 0.002; direction : "input"; }\n'
                 '      pin ("X") { direction : "output"; function : "A";\n'
                 + _arc("A", (0.010, 0.1, 2.0), (0.008, 0.1, 1.5), (0.005, 0.2, 3.0), (0.004, 0.2, 2.5), sense="positive_unate")
                 + "      }\n    }\n")
    t.append("}\n")
    return "".join(t)


def write_pins(path, lib_path, buffers=("buf_1",), **over):
    """A pins file identical to the real one except for the liberty's identity, the repair's buffer cells and the default
    input drive (the synthetic liberty has buf_1 only) and any override of a liberty key."""
    with open(ppa.PINS_PATH) as fh:
        raw = json.load(fh)
    raw["timing"]["input_drive"]["default"] = PREFIX + "buf_1"
    raw["liberty"]["sha256"] = ppa.sha256_file(lib_path)
    raw["liberty"]["bytes"] = os.path.getsize(lib_path)
    raw["liberty"].update(over)
    if buffers is not None:
        raw["repair"]["buffers"] = list(buffers)
    with open(path, "w") as fh:
        json.dump(raw, fh)
    return ppa.Pins(path)


def write_mapped_pins(path, pins, **over):
    """A mapped-flow pins file identical to the real one except for the liberty it names (the A0' pins' liberty) and any
    override of a top-level key; its script is the real score/ppa_mapped.ys."""
    with open(ppa.MAPPED_PINS_PATH) as fh:
        raw = json.load(fh)
    raw["liberty_sha256"] = pins.lib["sha256"]
    raw.update(over)
    with open(path, "w") as fh:
        json.dump(raw, fh)
    return ppa.MappedPins(pins, path=path)


def netlist(body, ports="input a;\n  input b;\n  output y;", wires=""):
    return f"module tiny(a, b, y);\n  {wires}\n  {ports}\n{body}endmodule\n"


def gate(kind, inst, **pins):
    p = ",\n".join(f"    .{k}({v})" for k, v in pins.items())
    return f"  \\$_{kind}_  {inst} (\n{p}\n  );\n"


TINY = netlist(gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="y"), wires="wire _0_;")


class MiniLibTest(unittest.TestCase):
    """The tiny netlist `y = nand(not(a), b)` on the synthetic liberty, hand-computed."""

    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="ppa-test-")
        cls.libp = os.path.join(cls.dir, "mini.lib")
        with open(cls.libp, "w") as fh:
            fh.write(mini_lib())
        cls.pinsp = os.path.join(cls.dir, "pins.json")
        cls.pins = write_pins(cls.pinsp, cls.libp)
        cls.lib = ppa.Liberty(cls.libp, cls.pins)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    def analyze(self, text):
        return ppa.analyze(text, self.lib, self.pins)

    # The primary inputs are driven by buf_1 (the synthetic pins' default input drive) whose input is the 50 ps ideal ramp:
    #   a (load inv_1.A 0.002): rise 0.010 + 0.1*0.05 + 2*0.002 = 0.019, slew 0.005 + 0.2*0.05 + 3*0.002 = 0.021;
    #                           fall 0.008 + 0.005 + 1.5*0.002 = 0.016, slew 0.004 + 0.01 + 2.5*0.002 = 0.019
    #   b (load nand2_1.B 0.003): rise 0.021, slew 0.024; fall 0.0175, slew 0.0215
    # inv_1 drives nand2_1.A (0.003 pF):
    #   output rising (a falling, 0.016 / 0.019): d = 0.020 + 0.5*0.019 + 5*0.003 = 0.0445 -> 0.0605, slew 0.015 + 0.3*0.019 + 0.03 = 0.0507
    #   output falling (a rising, 0.019 / 0.021): d = 0.010 + 0.4*0.021 + 4*0.003 = 0.0304 -> 0.0494, slew 0.012 + 0.2*0.021 + 0.024 = 0.0402
    INV_FALL, INV_FALL_SLEW, INV_RISE, INV_RISE_SLEW = 0.0494, 0.0402, 0.0605, 0.0507

    def test_hand_computed_delay_and_area(self):
        """PO 10 fF = 0.010 pF, inputs driven by buf_1 (above).
        nand2 rising (inputs falling): via A 0.0494 + (0.030 + 0.6*0.0402 + 6*0.010) = 0.16352; via B 0.0175 + 0.035 + 0.6*0.0215 + 0.06 = 0.1254
        nand2 falling (inputs rising): via A 0.0605 + (0.020 + 0.5*0.0507 + 5*0.010) = 0.15585; via B 0.021 + 0.025 + 0.5*0.024 + 0.05 = 0.108
        T = 0.16352 ns (the rising output through the inverter), area 3.75 + 5.0 = 8.75 um^2 (the driving cell is the
        environment's, not priced), 2 cells, depth 2. The repair finds nothing over a limit and changes nothing (the netlist
        it writes and reads back has the same cells and nets); without it the STA reads the netlist as written."""
        for repaired in (True, False):
            a = ppa.analyze(TINY, self.lib, self.pins, repair_netlist=repaired)
            self.assertAlmostEqual(a.t_ns, 0.16352, places=12)
            self.assertEqual(a.area_e4, 87500)
            self.assertEqual((a.cells, a.unit_depth, a.constants, a.scored_gates), (2, 2, False, 2))
            self.assertEqual(a.hist, {"inv_1": 1, "nand2_1": 1})
            self.assertEqual((a.crit_output, a.crit_edge, a.crit_cells), ("y", "r", 2))
            self.assertEqual([e for _, e, _ in a.path], ["r", "f", "r"])
            self.assertEqual((a.path[0][0], a.path[-1][0]), ("a", "y"))
            self.assertEqual(a.audit.summary()["table_reads_outside"], 0)
            self.assertEqual(a.path[1][0], "_0_")
        self.assertIsNone(a.repair)

    def test_the_ideal_ramp_sta_of_flow_a1(self):
        """Without a driving cell (flow A1''s setup, analyze_cells) every input is the ideal 50 ps ramp:
        inv rising d = 0.020 + 0.5*0.05 + 5*0.003 = 0.060, slew 0.060; falling d = 0.042, slew 0.046;
        nand2 falling via A 0.060 + 0.020 + 0.5*0.060 + 0.050 = 0.160 (rising via A 0.042 + 0.030 + 0.6*0.046 + 0.06 = 0.1596)."""
        a = ppa.analyze_cells(ppa.expand_a0(ppa.parse_netlist(TINY), self.pins), self.lib, self.pins)
        self.assertAlmostEqual(a.t_ns, 0.160, places=12)
        self.assertEqual([(n, e) for n, e, _ in a.path], [("a", "f"), ("_0_", "r"), ("y", "f")])
        self.assertIsNone(a.audit)

    def test_flow_a1_still_extrapolates_and_the_ranked_flow_never_does(self):
        """Three output bits (0.030 pF, past the 0.02 pF grid): flow A1' (unranked, sky130_a1_v1, unchanged by the 11/04
        ruling) reads the linear extrapolation as it always did, exact here because the tables are linear: nand2 rising via A
        0.042 + 0.030 + 0.6*0.046 + 6*0.030 = 0.2796. The ranked flow never reads past the grid: as written it rejects the
        netlist, repaired it buffers the net (test_load_beyond_the_grid_is_buffered_never_extrapolated)."""
        text = netlist(gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="_3_")
                       + "  assign y = _3_;\n  assign z = _3_;\n  assign w = _3_;\n",
                       ports="input a;\n  input b;\n  output y;\n  output z;\n  output w;", wires="wire _0_;\n  wire _3_;")
        a = ppa.analyze_cells(ppa.expand_a0(ppa.parse_netlist(text), self.pins), self.lib, self.pins)
        self.assertAlmostEqual(a.t_ns, 0.2796, places=12)
        with self.assertRaises(ppa.IllegalNetlist):
            ppa.analyze(text, self.lib, self.pins, repair_netlist=False)
        self.assertEqual(ppa.analyze(text, self.lib, self.pins).hist, {"buf_1": 2, "inv_1": 1, "nand2_1": 1})

    def test_columns(self):
        c = ppa.weigh_netlist_text(TINY, self.lib, self.pins)
        self.assertEqual((c["area_um2_sky130"], c["area_e4um2_sky130"], c["delay_ps_sky130"], c["unit_depth"]),
                         (8.75, 87500, 164, 2))
        self.assertEqual(c["ppa_version"], self.pins.version)
        self.assertEqual(c["liberty_sha256"], ppa.sha256_file(self.libp))
        self.assertEqual(c["ppa_pins_sha256"], ppa.sha256_file(self.pinsp))
        self.assertEqual(c["ppa_script_sha256"], ppa.sha256_file(os.path.join(HERE, "ppa.py")))
        self.assertEqual(c["setup"], {"pi_slew_ps": 50, "input_drive": PREFIX + "buf_1", "po_load_ff": 10, "wires": "none",
                                      "tables": "no extrapolation"})
        self.assertEqual(c["legality"]["over_max_capacitance"] + c["legality"]["over_max_transition"]
                         + c["legality"]["table_reads_outside"], 0)
        r = c["repair"]
        self.assertEqual(r, {"method": "buffer_trees_v1", "cells_before": 2, "buffers": 0, "nets_buffered": 0, "tie_cells": 0,
                             "rounds": 1, "netlist_sha256": r["netlist_sha256"]})
        self.assertRegex(r["netlist_sha256"], "^[0-9a-f]{64}$")

    def test_load_is_per_output_bit_and_assign_is_followed(self):
        """Two output bits on one net load it twice: PO load 0.020 pF.
        nand2 rising via A: 0.0494 + 0.030 + 0.6*0.0402 + 6*0.020 = 0.22352; falling via A: 0.0605 + 0.020 + 0.02535 + 5*0.020 = 0.20585."""
        text = netlist(gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="_3_")
                       + "  assign y = _3_;\n  assign z = _3_;\n",
                       ports="input a;\n  input b;\n  output y;\n  output z;", wires="wire _0_;\n  wire _3_;")
        a = self.analyze(text)
        self.assertAlmostEqual(a.t_ns, 0.22352, places=12)
        self.assertEqual((a.crit_edge, a.crit_output), ("r", "y"))

    def test_load_beyond_the_grid_is_buffered_never_extrapolated(self):
        """Three output bits on one net: 0.030 pF, past the 0.02 pF end of the table. sky130_a0_v1 extrapolated linearly. As
        written the netlist is ILLEGAL: IllegalNetlist names the cell (nand2_1, the instance, the net) and the point, and no
        number comes out. The repair splits the three bits, in port order, over two buf_1 (10 fF and 20 fF: the synthetic
        buf_1 may carry its grid's 20 fF; the balanced cut takes the earlier of two equally near points) and weighs that."""
        text = netlist(gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="_3_")
                       + "  assign y = _3_;\n  assign z = _3_;\n  assign w = _3_;\n",
                       ports="input a;\n  input b;\n  output y;\n  output z;\n  output w;", wires="wire _0_;\n  wire _3_;")
        with self.assertRaises(ppa.IllegalNetlist) as cm:
            ppa.analyze(text, self.lib, self.pins, repair_netlist=False)
        msg = str(cm.exception)
        self.assertIn("1 cells read outside their timing tables", msg)
        self.assertIn("nand2_1 _2_ driving net _3_: input transition", msg)
        self.assertIn("load 30.0 fF, table grid 0 to 100 ps x 0 to 20 fF (1.50x)", msg)
        self.assertEqual(cm.exception.summary["cells_outside_tables"], 1)
        a = ppa.analyze(text, self.lib, self.pins)
        self.assertEqual(a.hist, {"buf_1": 2, "inv_1": 1, "nand2_1": 1})
        s = a.audit.summary()
        self.assertEqual((s["table_reads_outside"], s["over_max_capacitance"], s["over_max_transition"]), (0, 0, 0))
        self.assertEqual(a.repair["nets"], 1)
        rep = ppa.parse_netlist(a.repair["text"])            # the tree, in the repaired netlist itself
        bufs = [g for g in rep.gates if g.kind == PREFIX + "buf_1"]
        self.assertEqual([g.pins["A"] for g in bufs], ["_3_", "_3_"])
        driven = {g.pins["X"]: [p for p, _, n in rep.po if rep.resolve(n) == g.pins["X"]] for g in bufs}
        self.assertEqual(sorted(driven.values()), [["y"], ["z", "w"]])
        with self.assertRaises(ppa.TableRange):           # and the table itself refuses to extrapolate
            self.lib.cell(PREFIX + "nand2_1").arcs["Y"][0].tbl["cell_rise"].at(0.05, 0.030)

    def test_constants_cost_one_tie_cell_and_no_delay(self):
        """A constant on a cell pin or an output bit: ONE conb_1 (3.75 um^2, one cell), none otherwise."""
        const_in = netlist(gate("NOT", "_1_", A="1'h0", Y="y"), ports="input a;\n  input b;\n  output y;")
        a = self.analyze(const_in)
        self.assertEqual((a.area_e4, a.cells, a.constants, a.t_ns), (75000, 2, True, 0.0))
        self.assertEqual(a.hist, {"conb_1": 1, "inv_1": 1})
        const_out = netlist("  assign y = 1'h1;\n")
        a = self.analyze(const_out)
        self.assertEqual((a.area_e4, a.cells, a.constants, a.unit_depth), (37500, 1, True, 0))
        a = self.analyze(TINY)
        self.assertFalse(a.constants)
        two = netlist(gate("NOT", "_1_", A="1'h0", Y="y") + "  assign z = 1'h1;\n",
                      ports="input a;\n  input b;\n  output y;\n  output z;")
        self.assertEqual(self.analyze(two).cells, 2)       # still ONE tie cell for any number of constants

    def test_deterministic_across_processes_and_hash_seeds(self):
        net = os.path.join(self.dir, "tiny.v")
        with open(net, "w") as fh:
            fh.write(TINY)
        outs = []
        for seed in ("0", "1", "123"):
            env = dict(os.environ, PYTHONHASHSEED=seed, PYTHONDONTWRITEBYTECODE="1")
            r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), "--netlist-in", net, "--liberty",
                                self.libp, "--pins", self.pinsp, "--path"], capture_output=True, text=True, env=env)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            outs.append(r.stdout)
        self.assertEqual(outs[0], outs[1])
        self.assertEqual(outs[0], outs[2])
        res = json.loads(outs[0])
        self.assertEqual(res["ppa"]["delay_ps_sky130"], 164)
        path = res["ppa"]["critical_path"]
        self.assertEqual((path[0], path[-1], len(path)), (["a", "r"], ["y", "r"], 3))

    # -- flow A1' (WP-X4) on the synthetic liberty: the same STA on a mapped netlist, the equivalence sample
    def mapped(self, body, wires="", **kw):
        return netlist(body, wires=wires, **kw)

    MAPPED_TINY = (f"  {PREFIX}inv_1  _1_ (\n    .A(a),\n    .Y(_0_)\n  );\n"
                   f"  {PREFIX}nand2_1  _2_ (\n    .A(_0_),\n    .B(b),\n    .Y(y)\n  );\n")

    def mpins(self, **over):
        return write_mapped_pins(os.path.join(self.dir, "mapped_pins.json"), self.pins, **over)

    def test_a_mapped_netlist_is_weighed_by_the_same_sta(self):
        """The mapped netlist is `inv_1` + `nand2_1` again: the hand computation of A0' (T = 0.160 ns, 8.75 um^2) applies."""
        nl, a = ppa.analyze_mapped(self.mapped(self.MAPPED_TINY, wires="wire _0_;"), self.lib, self.pins)
        self.assertAlmostEqual(a.t_ns, 0.160, places=12)
        self.assertEqual((a.area_e4, a.cells, a.unit_depth, a.hist), (87500, 2, 2, {"inv_1": 1, "nand2_1": 1}))
        b = ppa.analyze_mapped(self.mapped(self.MAPPED_TINY, wires="wire _0_;"), self.lib, self.pins)[1]
        c = ppa.mapped_columns(b, self.pins, self.mpins(), self.lib, "e" * 64, "f" * 64, "Yosys x", "ABC x", 2048)
        self.assertEqual((c["area_um2_sky130_mapped_v1"], c["area_e4um2_sky130_mapped_v1"], c["mapped_delay_sky130_v1"],
                          c["mapped_cells_sky130_v1"], c["mapped_levels_sky130_v1"], c["mapped_buffers_sky130_v1"],
                          c["mapped_inverters_sky130_v1"]), (8.75, 87500, 160, 2, 2, 0, 1))
        self.assertEqual(c["mapped_cell_hist_sky130_v1"], {"inv_1": 1, "nand2_1": 1})
        self.assertEqual((c["rtlil_sha256"], c["netlist_sha256"], c["yosys_version"], c["abc_version"]),
                         ("f" * 64, "e" * 64, "Yosys x", "ABC x"))
        self.assertEqual(c["liberty_sha256"], ppa.sha256_file(self.libp))
        self.assertEqual(c["ppa_mapped_pins_sha256"], ppa.sha256_file(os.path.join(self.dir, "mapped_pins.json")))
        self.assertEqual(c["ppa_mapped_script_sha256"], ppa.sha256_file(ppa.MAPPED_SCRIPT_PATH))
        self.assertEqual(c["setup"], {"pi_slew_ps": 50, "po_load_ff": 10, "wires": "none"})

    def test_the_two_flows_never_share_a_field_name(self):
        """A0' and A1' fields are never swapped silently: the mapped block uses none of A0''s column names."""
        a = self.analyze(TINY)
        a0 = ppa.columns(a, self.pins, self.lib, "x")
        m = ppa.mapped_columns(a, self.pins, self.mpins(), self.lib, "e" * 64, "f" * 64, "Y", "A", 2048)
        shared = sorted(set(a0) & set(m))
        self.assertEqual(shared, ["constants", "critical", "liberty_file", "liberty_sha256", "netlist_sha256", "ppa_pins_sha256",
                                  "ppa_script_sha256", "setup"])     # provenance, same meaning in both
        for k in ("area_um2_sky130", "area_e4um2_sky130", "delay_ps_sky130", "unit_depth", "cells_sky130", "cell_hist_sky130",
                  "ppa_version"):
            self.assertNotIn(k, m, k)
        self.assertNotEqual(m["ppa_mapped_version"], a0["ppa_version"])

    def test_constants_in_a_mapped_netlist_cost_one_tie_cell(self):
        text = netlist(f"  {PREFIX}inv_1  _1_ (\n    .A(1'h0),\n    .Y(y)\n  );\n  assign z = 1'h1;\n",
                       ports="input a;\n  input b;\n  output y;\n  output z;")
        a = ppa.analyze_mapped(text, self.lib, self.pins)[1]
        self.assertEqual((a.area_e4, a.cells, a.constants, a.hist), (75000, 2, True, {"conb_1": 1, "inv_1": 1}))

    def test_a_mapped_netlist_with_foreign_instances_is_refused(self):
        for kind in ("\\$_AND_ ", f"{PREFIX}nosuchcell_1", "other_lib__inv_1", f"{PREFIX}dfxtp_1"):
            text = netlist(f"  {kind}  _1_ (\n    .A(a),\n    .Y(y)\n  );\n")
            with self.assertRaises(ppa.PpaError, msg=kind) as cm:
                ppa.analyze_mapped(text, self.lib, self.pins)
            self.assertIn("not cells of the pinned liberty", str(cm.exception))

    def test_equivalence_accepts_the_same_function_written_differently(self):
        scored = netlist(gate("NAND", "_1_", A="a", B="b", Y="y"))
        double_inverted = (f"  {PREFIX}nand2_1  _1_ (\n    .A(a),\n    .B(b),\n    .Y(_0_)\n  );\n"
                           f"  {PREFIX}inv_1  _2_ (\n    .A(_0_),\n    .Y(_3_)\n  );\n"
                           f"  {PREFIX}inv_1  _4_ (\n    .A(_3_),\n    .Y(y)\n  );\n")
        nl = ppa.parse_netlist(netlist(double_inverted, wires="wire _0_;\n  wire _3_;"))
        self.assertEqual(ppa.check_equivalent(scored, nl, self.lib, self.pins, self.mpins()), 2048)
        # and the tiny design against itself, constants included
        self.assertEqual(ppa.check_equivalent(TINY, ppa.parse_netlist(self.mapped(self.MAPPED_TINY, wires="wire _0_;")),
                                              self.lib, self.pins, self.mpins()), 2048)

    def test_equivalence_catches_a_different_function(self):
        """The mapped netlist drops the input inverter: `nand(a, b)` against the scored `nand(not(a), b)`. The sample finds it
        at once (vector 0 is all zeros), and it is a MappedDefect, the class check.py makes an infrastructure error."""
        wrong = netlist(f"  {PREFIX}nand2_1  _2_ (\n    .A(a),\n    .B(b),\n    .Y(y)\n  );\n")
        with self.assertRaises(ppa.MappedDefect) as cm:
            ppa.check_equivalent(TINY, ppa.parse_netlist(wrong), self.lib, self.pins, self.mpins())
        self.assertIn("differs from the scored netlist at output y[0] on vector", str(cm.exception))
        self.assertIsInstance(ppa.MappedDefect("x"), ppa.PpaError)
        other_ports = netlist(self.MAPPED_TINY, ports="input a;\n  input c;\n  output y;", wires="wire _0_;").replace("b", "c")
        with self.assertRaises(ppa.MappedDefect):
            ppa.check_equivalent(TINY, ppa.parse_netlist(other_ports), self.lib, self.pins, self.mpins())

    def test_the_stimulus_is_the_pinned_sha256_stream(self):
        """The equivalence sample is a function of nothing but the pins: vector 0 all zeros, vector 1 all ones, the other bits
        SHA-256(seed/input bit index/block), 256 vectors per block, little-endian."""
        stim = ppa.stimulus(["a", "b"], 256, "svgolf-ppa-mapped/1")
        want = (int.from_bytes(hashlib.sha256(b"svgolf-ppa-mapped/1/0/0").digest(), "little") & ~3) | 2
        self.assertEqual(stim["a"], want)
        self.assertEqual(stim["a"] & 3, 2)                       # bit 0 (vector 0) clear, bit 1 (vector 1) set: all zeros, all ones
        self.assertEqual(stim["b"] & 3, 2)
        self.assertLess(stim["a"], 1 << 256)
        self.assertNotEqual(stim["a"], stim["b"])
        self.assertEqual(stim, ppa.stimulus(["a", "b"], 256, "svgolf-ppa-mapped/1"))
        self.assertNotEqual(stim["a"], ppa.stimulus(["a"], 256, "svgolf-ppa-mapped/2")["a"])
        self.assertEqual(len(bin(ppa.stimulus(["a"], 2048, "s")["a"])) - 2 <= 2048, True)

    def test_mapped_pins_are_validated(self):
        self.assertEqual(self.mpins().version, json.load(open(ppa.MAPPED_PINS_PATH))["ppa_mapped_version"])
        with open(ppa.MAPPED_PINS_PATH) as fh:
            raw = json.load(fh)
        bad_lib = os.path.join(self.dir, "bad_lib_pins.json")
        raw2 = dict(raw)                                          # names the REAL liberty, the A0' pins here the mini one
        with open(bad_lib, "w") as fh:
            json.dump(raw2, fh)
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.MappedPins(self.pins, path=bad_lib)
        self.assertIn("one liberty", str(cm.exception))
        for over in ({"equivalence": {"vectors": 100, "seed": "x"}}, {"tools": {"yosys_version": "y"}},
                     {"yosys_timeout_s": 0}, {"yosys_timeout_s": "soon"}):
            with self.assertRaises(ppa.PpaError, msg=str(over)):
                self.mpins(**over)
        with self.assertRaises(ppa.PpaError):
            ppa.MappedPins(self.pins, path=os.path.join(self.dir, "absent.json"))
        with self.assertRaises(ppa.PpaError):
            ppa.MappedPins(self.pins, script=os.path.join(self.dir, "absent.ys"))

    def test_a_mapping_run_that_times_out_or_fails_is_a_reason(self):
        il = os.path.join(self.dir, "t.il")
        with open(il, "w") as fh:
            fh.write("module")
        score = ppa._score_module()
        mp = self.mpins()
        with mock.patch.object(score, "yosys_run", side_effect=subprocess.TimeoutExpired("yosys", 1)):
            with self.assertRaises(ppa.PpaError) as cm:
                ppa.map_rtlil(il, "top", self.lib, mp)
        self.assertIn(f"timed out after {mp.timeout_s} s", str(cm.exception))
        bad = subprocess.CompletedProcess(["yosys"], 1, stdout="", stderr="ERROR: boom\n   second line")
        with mock.patch.object(score, "yosys_run", return_value=bad):
            with self.assertRaises(ppa.PpaError) as cm:
                ppa.map_rtlil(il, "top", self.lib, mp)
        self.assertIn("the mapping run failed (exit 1): ERROR: boom second line", str(cm.exception))
        with mock.patch.object(score, "yosys_run", side_effect=FileNotFoundError("no yosys")):
            with self.assertRaises(ppa.PpaError):
                ppa.map_rtlil(il, "top", self.lib, mp)
        ok = subprocess.CompletedProcess(["yosys"], 0, stdout="", stderr="")
        with mock.patch.object(score, "yosys_run", return_value=ok):         # exit 0 and no netlist: still loud
            with self.assertRaises(ppa.PpaError) as cm:
                ppa.map_rtlil(il, "top", self.lib, mp)
        self.assertIn("wrote no readable netlist", str(cm.exception))

    def test_mapped_block_says_why_and_a_defect_is_not_swallowed(self):
        il = os.path.join(self.dir, "x.il")
        b = ppa.mapped_block(os.path.join(self.dir, "absent.il"), "top", TINY, self.lib, self.pins, self.mpins())
        self.assertFalse(b["available"])
        self.assertIn("cannot read the canonical RTLIL", b["reason"])
        with open(il, "w") as fh:
            fh.write("module")
        with mock.patch.object(ppa, "map_rtlil", side_effect=ppa.PpaError("the mapping run failed: boom\n  more")):
            b = ppa.mapped_block(il, "top", TINY, self.lib, self.pins, self.mpins())
        self.assertEqual(b, {"available": False, "reason": "the mapping run failed: boom more"})
        with mock.patch.object(ppa, "map_rtlil", return_value=netlist(self.MAPPED_TINY.replace("nand2_1", "nosuch_1"))):
            b = ppa.mapped_block(il, "tiny", TINY, self.lib, self.pins, self.mpins())
        self.assertFalse(b["available"])
        self.assertIn("not cells of the pinned liberty", b["reason"])
        wrong = netlist(f"  {PREFIX}nand2_1  _2_ (\n    .A(a),\n    .B(b),\n    .Y(y)\n  );\n")
        with mock.patch.object(ppa, "map_rtlil", return_value=wrong), \
                mock.patch.object(ppa, "abc_version", return_value="ABC x"), \
                mock.patch.object(ppa._score_module(), "yosys_version", return_value="Yosys x"):
            with self.assertRaises(ppa.MappedDefect):
                ppa.mapped_block(os.path.join(self.dir, "x.il"), "tiny", TINY, self.lib, self.pins, self.mpins())

    def test_a_good_mapping_through_the_driver_gives_the_block(self):
        with open(os.path.join(self.dir, "x.il"), "w") as fh:
            fh.write("module")
        with mock.patch.object(ppa, "map_rtlil", return_value=netlist(self.MAPPED_TINY, wires="wire _0_;")), \
                mock.patch.object(ppa, "abc_version", return_value="ABC x"), \
                mock.patch.object(ppa._score_module(), "yosys_version", return_value="Yosys x"):
            out = os.path.join(self.dir, "mapped_out.v")
            b = ppa.mapped_block(os.path.join(self.dir, "x.il"), "tiny", TINY, self.lib, self.pins, self.mpins(),
                                 netlist_out=out)
        self.assertTrue(b["available"])
        self.assertEqual((b["area_e4um2_sky130_mapped_v1"], b["mapped_delay_sky130_v1"], b["equivalence"]["vectors"]),
                         (87500, 160, 2048))
        with open(out) as fh:
            self.assertEqual(ppa.sha256_bytes(fh.read().encode()), b["netlist_sha256"])
        self.assertEqual(b["rtlil_sha256"], ppa.sha256_file(os.path.join(self.dir, "x.il")))

    # -- failure modes: loud, never a silent number
    def test_missing_liberty_is_loud(self):
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.Liberty(os.path.join(self.dir, "absent.lib"), self.pins)
        self.assertIn("--fetch-liberty", str(cm.exception))
        net = os.path.join(self.dir, "tiny.v")
        with open(net, "w") as fh:
            fh.write(TINY)
        r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), "--netlist-in", net, "--liberty",
                            os.path.join(self.dir, "absent.lib"), "--pins", self.pinsp], capture_output=True, text=True)
        self.assertEqual(r.returncode, 1)
        self.assertIn("liberty not found", json.loads(r.stdout)["error"])

    @unittest.skipIf(not hasattr(os, "geteuid") or os.geteuid() == 0, "root reads a mode-000 file")
    def test_an_unreadable_liberty_is_loud_not_a_traceback(self):
        """A file that exists but cannot be read (permissions): a PpaError like an absent one (check.py and the suite
        catch exactly that), on the library and on the CLI."""
        locked = os.path.join(self.dir, "locked.lib")
        shutil.copyfile(self.libp, locked)
        os.chmod(locked, 0)
        self.addCleanup(os.chmod, locked, 0o600)
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.Liberty(locked, self.pins)
        self.assertIn("cannot be read", str(cm.exception))
        net = os.path.join(self.dir, "tiny.v")
        with open(net, "w") as fh:
            fh.write(TINY)
        r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), "--netlist-in", net, "--liberty", locked,
                            "--pins", self.pinsp], capture_output=True, text=True)
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("cannot be read", json.loads(r.stdout)["error"])

    def test_wrong_liberty_is_loud(self):
        other = os.path.join(self.dir, "other.lib")
        with open(other, "w") as fh:
            fh.write(mini_lib().replace("3.7500000000", "3.7600000000"))
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.Liberty(other, self.pins)           # pinned to the other file's hash
        self.assertIn("sha256", str(cm.exception))

    def test_cells_outside_the_table_are_refused(self):
        for kind in ("DFF_P", "TBUF", "SDFF_PP0", "DLATCH_P", "NMUX"):
            text = netlist(f"  \\$_{kind}_  _1_ (\n    .A(a),\n    .Y(y)\n  );\n")
            with self.assertRaises(ppa.PpaError, msg=kind) as cm:
                self.analyze(text)
            self.assertIn(f"$_{kind}_", str(cm.exception))
        mapped = netlist(f"  {PREFIX}a21oi_1  _1_ (\n    .A1(a),\n    .A2(b),\n    .B1(b),\n    .Y(y)\n  );\n")
        with self.assertRaises(ppa.PpaError) as cm:
            self.analyze(mapped)
        self.assertIn("a21oi_1", str(cm.exception))

    def test_bad_pins_nets_and_loops(self):
        cases = {
            "pins": netlist(gate("NAND", "_1_", A="a", Y="y")),
            "never driven": netlist(gate("NOT", "_1_", A="ghost", Y="y")),
            "driven by two": netlist(gate("NOT", "_1_", A="a", Y="y") + gate("NOT", "_2_", A="b", Y="y")),
            "primary input": netlist(gate("NOT", "_1_", A="b", Y="a") + gate("NOT", "_2_", A="a", Y="y")),
            "loop": netlist(gate("NOT", "_1_", A="_1n_", Y="_0_") + gate("NOT", "_2_", A="_0_", Y="_1n_")
                            + gate("NAND", "_3_", A="_0_", B="b", Y="y"), wires="wire _0_;\n  wire _1n_;"),
        }
        for want, text in cases.items():
            with self.assertRaises(ppa.PpaError, msg=want) as cm:
                self.analyze(text)
            self.assertIn(want, str(cm.exception))

    def test_escaped_identifiers_and_the_dead_wires_of_expanded_cells(self):
        """Yosys leaves the public-named wires of a techmapped cell (`$shiftx`, `$pmux`, `$div`, ...) in the netlist:
        `wire [7:0] \\_1_.A ;` (an escaped identifier is ended by a space), `assign \\_1_.A  = a;`, a part select after the
        space (`\\_1_.B [2:1]`), brackets inside a name (`\\_1_.stage[1].x `), and constants with x bits. They parse; when
        no gate reads them they change nothing; when a gate drives one they carry the signal."""
        dead = ("module tiny(a, b, y);\n  wire _0_;\n  wire [7:0] \\_1_.A ;\n  wire [2:0] \\_1_.B ;\n"
                "  wire [7:0] \\_1_.buffer ;\n  wire \\_1_.stage[1].x ;\n  input a;\n  input b;\n  output y;\n"
                + gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="y")
                + "  assign \\_1_.A  = { a, a, a, a, b, b, b, b };\n  assign \\_1_.B [2:1] = { a, b };\n"
                  "  assign \\_1_.buffer [7:4] = 4'hx;\n  assign { \\_1_.buffer [3:2], \\_1_.buffer [0] } = { 2'hx, y };\n"
                  "  assign \\_1_.stage[1].x  = \\_1_.A [3];\nendmodule\n")
        want = self.analyze(TINY)
        got = self.analyze(dead)
        self.assertEqual((got.area_e4, got.t_ns, got.cells, got.unit_depth, got.hist),
                         (want.area_e4, want.t_ns, want.cells, want.unit_depth, want.hist))
        # a gate that drives an escaped wire, which an assign hands to the output (what a dynamic bit select leaves)
        live = netlist(gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="\\_2_.Y ")
                       + "  assign y = \\_2_.Y ;\n", wires="wire _0_;\n  wire \\_2_.Y ;")
        got = self.analyze(live)
        self.assertEqual((got.area_e4, got.t_ns, got.cells), (want.area_e4, want.t_ns, want.cells))
        # a vector whose range does not start at 0, used by a gate and by a dead wire
        offset = ("module tiny(v, y);\n  wire [8:1] \\_1_.W ;\n  input [8:1] v;\n  output y;\n"
                  + gate("NOT", "_1_", A="v[8]", Y="y") + "  assign \\_1_.W [8:5] = v[8:5];\n  assign \\_1_.W [1] = v[1];\nendmodule\n")
        got = self.analyze(offset)
        self.assertEqual((got.cells, got.hist, got.unit_depth), (1, {"inv_1": 1}, 1))

    def test_dead_wires_do_not_hide_a_malformed_netlist(self):
        """The reader is more tolerant of syntax, not of meaning: a width mismatch, an x bit that a gate or an output
        actually reads, and an undriven net are still refused."""
        head = "module tiny(a, b, y);\n  wire _0_;\n  wire [7:0] \\_1_.A ;\n  input a;\n  input b;\n  output y;\n"
        body = gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="y")
        with self.assertRaises(ppa.PpaError) as cm:
            self.analyze(head + body + "  assign \\_1_.A [3:0] = a;\nendmodule\n")
        self.assertIn("assign width mismatch", str(cm.exception))
        # y comes from an x bit: refused, though the x sits in an assign, not on a pin
        xout = head + gate("NOT", "_1_", A="a", Y="_0_") + "  assign \\_1_.A [0] = 1'hx;\n  assign y = \\_1_.A [0];\nendmodule\n"
        with self.assertRaises(ppa.PpaError) as cm:
            self.analyze(xout)
        self.assertIn("x/z constant", str(cm.exception))
        # a gate reads an x bit through a dead wire
        xin = head + gate("NOT", "_1_", A="\\_1_.A [0]", Y="y") + "  assign \\_1_.A [0] = 1'bz;\nendmodule\n"
        with self.assertRaises(ppa.PpaError) as cm:
            self.analyze(xin)
        self.assertIn("x/z constant", str(cm.exception))
        # an escaped wire nobody drives, read by a gate
        ghost = head + gate("NOT", "_1_", A="\\_1_.A [3]", Y="y") + "endmodule\n"
        with self.assertRaises(ppa.PpaError) as cm:
            self.analyze(ghost)
        self.assertIn("never driven", str(cm.exception))

    def test_x_and_z_constants_are_refused(self):
        for c in ("1'bx", "2'b0x", "1'hz"):
            with self.assertRaises(ppa.PpaError, msg=c):
                self.analyze(netlist(gate("NOT", "_1_", A=c, Y="y")))

    def test_escaped_port_names_are_read(self):
        # Yosys writes `input \\a[0] ;` (a space before the semicolon); such a port must be read, not dropped
        text = netlist(gate("NOT", "_1_", A="\\a[0] ", Y="\\y.z "), ports="input \\a[0] ;\n  output \\y.z ;")
        nl = ppa.parse_netlist(text)
        self.assertEqual(sorted(n for n, _, _ in nl.ports), ["\\a[0]", "\\y.z"])
        # a port line the parser cannot read is refused, never skipped
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.parse_netlist(netlist(gate("NOT", "_1_", A="a", Y="y"), ports="input a;\n  output [3 : 0] y;"))
        self.assertIn("unreadable port", str(cm.exception))

    def test_unreadable_netlists(self):
        for text in ("", "module a(x); endmodule\nmodule b(y); endmodule\n",
                     netlist("", ports="inout a;\n  input b;\n  output y;")):
            with self.assertRaises(ppa.PpaError):
                self.analyze(text)

    def test_library_defects_are_loud(self):
        def lib_with(**kw):
            p = os.path.join(self.dir, "defect.lib")
            with open(p, "w") as fh:
                fh.write(mini_lib(**kw))
            return ppa.Liberty(p, write_pins(os.path.join(self.dir, "defect.json"), p))
        # a cell the pin map needs is missing
        lib = lib_with(with_nand=False)
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze(TINY, lib, self.pins)
        self.assertIn("no cell", str(cm.exception))
        # the liberty's function disagrees with the Yosys gate the pin map says it implements
        lib = lib_with(inv_fn="(A)")
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze(TINY, lib, self.pins)
        self.assertIn("does not compute", str(cm.exception))
        # swapped table variables, other units
        with self.assertRaises(ppa.PpaError):
            ppa.analyze(TINY, lib_with(var2="input_net_transition"), self.pins)
        with self.assertRaises(ppa.PpaError):
            lib_with(cap_unit='"ff"')
        with self.assertRaises(ppa.PpaError):
            lib_with(time_unit='"1ps"')

    def test_policy_classes(self):
        for n, cls in (("inv_1", "logic"), ("mux4_2", "logic"), ("buf_16", "logic"), ("dfxtp_1", "sequential"),
                       ("sdfxtp_1", "sequential"), ("dlxtp_1", "sequential"), ("clkinv_1", "clock"),
                       ("conb_1", "tie"), ("fa_1", "multi-output"), ("ebufn_2", "tristate"),
                       ("lpflow_isobufsrc_1", "low-power-flow"), ("fill_1", "physical-only"), ("dlygate4sd1_1", "delay")):
            self.assertEqual(ppa.cell_class(PREFIX + n), cls, n)
        flop = netlist(f"  {PREFIX}dfxtp_1  _1_ (\n    .CLK(a),\n    .D(b),\n    .Q(y)\n  );\n")
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze_cells(ppa.parse_netlist(flop), self.lib, self.pins)
        self.assertIn("sequential", str(cm.exception))

    def test_fetch_checks_the_hash(self):
        src = os.path.join(self.dir, "src.lib")
        shutil.copyfile(self.libp, src)
        good = write_pins(os.path.join(self.dir, "fetch_good.json"), self.libp, url="file://" + src)
        dest = os.path.join(self.dir, "sub", "fetched.lib")
        self.assertEqual(ppa.fetch_liberty(dest, good), dest)
        self.assertEqual(ppa.sha256_file(dest), good.lib["sha256"])
        bad = os.path.join(self.dir, "bad.lib")
        with open(bad, "w") as fh:
            fh.write(mini_lib() + "\n")
        bad_pins = write_pins(os.path.join(self.dir, "fetch_bad.json"), self.libp, url="file://" + bad)
        dest2 = os.path.join(self.dir, "sub", "fetched2.lib")
        with self.assertRaises(ppa.PpaError):
            ppa.fetch_liberty(dest2, bad_pins)
        self.assertFalse(os.path.exists(dest2))
        self.assertFalse(os.path.exists(dest2 + ".part"))

    def test_kendall_tau(self):
        self.assertEqual(ppa_validate.kendall_tau([1, 2, 3, 4], [10, 20, 30, 40]), 1.0)
        self.assertEqual(ppa_validate.kendall_tau([1, 2, 3, 4], [4, 3, 2, 1]), -1.0)
        self.assertIsNone(ppa_validate.kendall_tau([1, 1, 1], [1, 2, 3]))
        # one tie in x: tau-b = (C - D) / sqrt((C + D + Tx)(C + D + Ty)) = 5 / sqrt(5 * 6)... pairs: 6, Tx = 1
        self.assertAlmostEqual(ppa_validate.kendall_tau([1, 1, 2, 3], [1, 2, 3, 4]), 5 / (5 * 6) ** 0.5, places=12)


# ------------------------------------------------------------------------------------------------ the real library
class RealLibraryRequired(unittest.TestCase):
    def test_liberty_present_when_required(self):
        if REQUIRE_LIB and not HAVE_LIB:
            self.fail(f"SVGOLF_PPA_REQUIRE_LIB=1 but the pinned liberty is absent: {REAL_LIB}")


@needs_lib
class RealLibraryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pins = REAL_PINS
        cls.lib = ppa.Liberty(REAL_LIB, cls.pins)

    def test_pinned_identity(self):
        self.assertEqual(self.lib.sha256, "ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5")
        self.assertEqual(os.path.getsize(REAL_LIB), 12800135)
        self.assertEqual(len(self.lib.cell_names), 428)
        self.assertEqual(self.pins.pi_slew_ns, 0.05)
        self.assertEqual(self.pins.po_load_pf, 0.010)

    def test_every_gate_cell_computes_its_gate(self):
        """The pin map of ppa_pins.json against the liberty's own boolean functions, truth table by truth table."""
        self.assertEqual(sorted(self.pins.gates), sorted(ppa.GATE_SEMANTICS))
        for g in self.pins.gates:
            ppa.check_gate_cell(self.lib, self.pins, g)

    def test_ge_ratios_of_sky130_md(self):
        """design/ppa/sky130.md section 2.1: the cell areas as GE (nand2_1 = 3.7536 um^2). NOT is 1.0 (ge.json 0.667), AND/OR
        1.667 (1.333), XOR/XNOR 2.333 (2.0), MUX 3.0 (2.333), ANDNOT/ORNOT single cells at 1.667 (1.333)."""
        with open(os.path.join(HERE, "ge.json")) as fh:
            legacy = {k: v for k, v in json.load(fh).items() if not k.startswith("_")}
        nand2 = self.lib.cell(PREFIX + "nand2_1").area_e4
        self.assertEqual(nand2, ppa.NAND2_E4)
        derived = {g: round(self.lib.cell(PREFIX + e["cell"]).area_e4 / nand2, 3) for g, e in self.pins.gates.items()}
        self.assertEqual(derived, {"NOT": 1.0, "NAND": 1.0, "NOR": 1.0, "AND": 1.667, "OR": 1.667, "XOR": 2.333,
                                   "XNOR": 2.333, "MUX": 3.0, "ANDNOT": 1.667, "ORNOT": 1.667})
        same = sorted(g for g in derived if abs(derived[g] - legacy[g]) < 5e-4)
        self.assertEqual(same, ["NAND", "NOR"])           # the other eight are repriced, as documented
        self.assertEqual(self.lib.cell(PREFIX + "conb_1").area_e4, 37536)
        with self.assertRaises(ppa.PpaError) as cm:                        # sequential timing arcs are out of scope: loud
            self.lib.cell(PREFIX + "dfxtp_1")
        self.assertIn("rising_edge", str(cm.exception))

    def test_inverter_against_a_hand_interpolation(self):
        """One inv_1 driving one output bit: input slew 0.05 ns, load 0.010 pF. The four corner values are read off the
        liberty (cell_rise / cell_fall of inv_1, rows index_1 = 0.0230506, 0.0531329; columns index_2 = 0.00952062,
        0.0254232) and interpolated here independently of ppa.py."""
        def bil(v, s0, s1, l0, l1, s=0.05, l=0.010):
            ta, tb = (s - s0) / (s1 - s0), (l - l0) / (l1 - l0)
            return (v[0][0] * (1 - tb) + v[0][1] * tb) * (1 - ta) + (v[1][0] * (1 - tb) + v[1][1] * tb) * ta
        rise = bil([[0.078324, 0.1679452], [0.0903158, 0.1807958]], 0.0230506, 0.0531329, 0.00952062, 0.0254232)
        fall = bil([[0.0501644, 0.1030737], [0.0615784, 0.1142486]], 0.0230506, 0.0531329, 0.00952062, 0.0254232)
        text = netlist(gate("NOT", "_1_", A="a", Y="y"), ports="input a;\n  input b;\n  output y;")
        a = ppa.analyze_cells(ppa.expand_a0(ppa.parse_netlist(text), self.pins), self.lib, self.pins)    # the ideal-ramp STA
        self.assertAlmostEqual(a.t_ns, max(rise, fall), places=12)
        self.assertGreater(rise, fall)
        self.assertEqual((a.crit_edge, a.area_e4, a.cells, a.unit_depth), ("r", 37536, 1, 1))
        c = ppa.columns(a, self.pins, self.lib, "x")
        self.assertEqual((c["delay_ps_sky130"], c["area_um2_sky130"]), (92, 3.7536))

    def test_the_driving_cell_against_a_hand_interpolation(self):
        """sky130_a0_v3: the input `a` of one inv_1 is the output of the task's input drive, here buf_1, whose own input is the
        50 ps ideal ramp, at a's load per edge (inv_1.A: rise_capacitance 0.00239 pF for a rising a, fall_capacitance
        0.002214 pF for a falling one, as OpenSTA reads them; its `capacitance` 0.002302 pF is not what timing reads).
        buf_1's cell_rise / cell_fall corners at rows index_1 = 0.0230506, 0.0531329 and columns index_2 = 0.00126321,
        0.00319137, read off the liberty, interpolated here; the output is then inv_1 at the transition buf_1 gives (checked
        through the STA's own arrival of `a`)."""
        def bil(v, s0, s1, l0, l1, l, s=0.05):
            ta, tb = (s - s0) / (s1 - s0), (l - l0) / (l1 - l0)
            return (v[0][0] * (1 - tb) + v[0][1] * tb) * (1 - ta) + (v[1][0] * (1 - tb) + v[1][1] * tb) * ta
        tbl = self.lib.cell(PREFIX + "buf_1").arcs["X"][0].tbl
        corners = {k: [row[1:3] for row in tbl[k].v[1:3]] for k in ("cell_rise", "cell_fall")}
        self.assertEqual((tbl["cell_rise"].i1[1:3], tbl["cell_rise"].i2[1:3]), ([0.0230506, 0.0531329], [0.0012632100, 0.0031913700]))
        rise = bil(corners["cell_rise"], 0.0230506, 0.0531329, 0.00126321, 0.00319137, 0.00239)
        fall = bil(corners["cell_fall"], 0.0230506, 0.0531329, 0.00126321, 0.00319137, 0.002214)
        text = netlist(gate("NOT", "_1_", A="a", Y="y"), ports="input a;\n  input b;\n  output y;")
        a = ppa.analyze(text, self.lib, self.pins, repair_netlist=False, input_drive=BUF1)
        arr = a.design.arr
        self.assertAlmostEqual(arr[("a", "r")][0], rise, places=12)
        self.assertAlmostEqual(arr[("a", "f")][0], fall, places=12)
        self.assertNotIn(("b", "r"), arr)                  # an input nothing reads has no arrival (and costs nothing)
        ideal = ppa.analyze_cells(ppa.expand_a0(ppa.parse_netlist(text), self.pins), self.lib, self.pins)
        self.assertGreater(a.t_ns, ideal.t_ns)              # inputs are not free any more
        b8 = ppa.analyze(text, self.lib, self.pins, repair_netlist=False)      # the default, buf_8: not free either
        self.assertEqual(b8.input_drive, PREFIX + "buf_8")
        self.assertGreater(b8.t_ns, ideal.t_ns)

    def test_and_gate_takes_the_worse_arc(self):
        """and2_1 (positive unate on both pins) at the same load; the B arc is the slower one for both edges. Corners at rows
        0.0230506, 0.0531329 and columns index_2 = 0.00889933, 0.0232356 of cell_rise / cell_fall of the B arc."""
        def bil(v, s0, s1, l0, l1, s=0.05, l=0.010):
            ta, tb = (s - s0) / (s1 - s0), (l - l0) / (l1 - l0)
            return (v[0][0] * (1 - tb) + v[0][1] * tb) * (1 - ta) + (v[1][0] * (1 - tb) + v[1][1] * tb) * ta
        rise = bil([[0.1502857, 0.2446479], [0.1594235, 0.2536776]], 0.0230506, 0.0531329, 0.00889933, 0.0232356)
        fall = bil([[0.1689204, 0.22173], [0.1822106, 0.2351275]], 0.0230506, 0.0531329, 0.00889933, 0.0232356)
        text = netlist(gate("AND", "_1_", A="a", B="b", Y="y"))
        a = ppa.analyze_cells(ppa.expand_a0(ppa.parse_netlist(text), self.pins), self.lib, self.pins)    # the ideal-ramp STA
        self.assertAlmostEqual(a.t_ns, max(rise, fall), places=12)
        self.assertEqual((a.crit_edge, a.area_e4), ("f", 62560))
        self.assertEqual(a.path[0][0], "b")

    def test_andnot_and_ornot_are_single_cells(self):
        text = netlist(gate("ANDNOT", "_1_", A="a", B="b", Y="_0_") + gate("ORNOT", "_2_", A="_0_", B="b", Y="y"),
                       wires="wire _0_;")
        a = ppa.analyze(text, self.lib, self.pins, repair_netlist=False)
        self.assertEqual((a.area_e4, a.cells, a.unit_depth, a.hist), (125120, 2, 2, {"nand2b_1": 1, "nor2b_1": 1}))

    def test_selective_parse_equals_full_parse(self):
        """A cell tokenized alone gives the same tables as the same cell inside a tokenization of the whole file."""
        whole = ppa._parse_group_text(self.lib._text)
        groups = {g.args[0]: g for g in whole.find("cell")}
        self.assertEqual(sorted(groups), self.lib.cell_names)
        for name in ("inv_1", "nand2b_1", "mux2_1", "xor2_1", "a21oi_1"):
            full = ppa.Cell(groups[PREFIX + name], self.lib.templates)
            alone = self.lib.cell(PREFIX + name)
            self.assertEqual((full.area_e4, full.pin_cap, full.function), (alone.area_e4, alone.pin_cap, alone.function))
            for op in full.outputs:
                self.assertEqual(len(full.arcs[op]), len(alone.arcs[op]))
                for x, y in zip(full.arcs[op], alone.arcs[op]):
                    self.assertEqual((x.related, x.sense), (y.related, y.sense))
                    for k in x.tbl:
                        self.assertEqual((x.tbl[k].i1, x.tbl[k].i2, x.tbl[k].v), (y.tbl[k].i1, y.tbl[k].i2, y.tbl[k].v))

    def test_every_logic_cell_parses_or_refuses_loudly(self):
        """Each `logic`-class cell of the library loads into tables or raises PpaError: nothing is skipped silently."""
        n = bad = 0
        for name in self.lib.cell_names:
            if ppa.cell_class(name) != "logic":
                continue
            n += 1
            try:
                c = self.lib.cell(name)
                self.assertTrue(c.outputs)
            except ppa.PpaError:
                bad += 1
        self.assertGreater(n, 250)
        self.assertEqual(bad, 0)


def fanout_netlist(k=100):
    """`n = !a` read by k nand2 gates, `y[i] = !(n & b)`: n (inv_1, max_capacitance 181 fF) and the input b (buf_1, 130 fF)
    each carry k * ~2.3 fF, far over their limits as written; the repair buffers both."""
    body = gate("NOT", "_n_", A="a", Y="n")
    body += "".join(gate("NAND", f"_g{i}_", A="n", B="b", Y=f"y[{i}]") for i in range(k))
    return netlist(body, ports=f"input a;\n  input b;\n  output [{k - 1}:0] y;", wires="wire n;")


def broadcast_netlist(k=20):
    """The input `a` drives k output bits directly (`assign y = {a, a, ...}`) beside one gate: k * 10 fF on the input's
    buf_1 (max_capacitance 130 fF). No cell drives that net: an `abc` repair never saw it; this one buffers it."""
    return netlist(gate("NOT", "_1_", A="b", Y="z") + "  assign y = {" + ", ".join(["a"] * k) + "};\n",
                   ports=f"input a;\n  input b;\n  output [{k - 1}:0] y;\n  output z;")


def shapes():
    """The review's probes as scored netlists (what the pinned flow writes for them), {name: (netlist, the net to buffer or
    None for the tie cells)}: each is ILLEGAL as written and its load is invisible to an `abc` repair (an input or a flop Q
    wired to output bits or D pins, constants), or legal high fan-out."""
    out = {}
    for k in (14, 64):                                    # an input wired to k output bits
        out[f"input_to_{k}_bits"] = (broadcast_netlist(k), "a")
    # sign extension {{16{x[15]}}, x}: x[15] drives 17 output bits
    out["signext_16_32"] = ("module t(x, y);\n  input [15:0] x;\n  output [31:0] y;\n  assign y = { "
                            + ", ".join(["x[15]"] * 16) + ", x };\nendmodule\n", "x[15]")
    for k in (17, 64):                                    # a flop's Q wired to k output bits
        out[f"q_to_{k}_bits"] = ("module t(clk, a, y);\n  input clk;\n  input a;\n  output [%d:0] y;\n  wire r0;\n" % (k - 1)
                                 + gate("DFF_P", "_r0_", C="clk", D="a", Q="r0") + "  assign y = { "
                                 + ", ".join(["r0"] * k) + " };\nendmodule\n", "r0")
    # an input into 96 flop D pins
    out["input_to_96_d"] = ("module t(clk, a, y);\n  input clk;\n  input a;\n  output [95:0] y;\n"
                            + "".join(gate("DFF_P", f"_f{i}_", C="clk", D="a", Q=f"y[{i}]") for i in range(96))
                            + "endmodule\n", "a")
    # {24{a & b}} beside other logic: one and2 net to 24 output bits
    out["and_to_24_bits"] = ("module t(a, b, c, y, z);\n  input a;\n  input b;\n  input c;\n  output [23:0] y;\n  output z;\n"
                             "  wire w;\n" + gate("AND", "_1_", A="a", B="b", Y="w") + gate("XOR", "_2_", A="w", B="c", Y="z")
                             + "  assign y = { " + ", ".join(["w"] * 24) + " };\nendmodule\n", "w")
    for k in (256, 1024):                                 # constant output bits: the tie cell
        out[f"const_{k}_bits"] = ("module t(a, y);\n  input a;\n  output [%d:0] y;\n  assign y = { %d'b0, a };\nendmodule\n"
                                  % (k - 1, k - 1), None)
    out["const_hi_lo"] = ("module t(a, y);\n  input [7:0] a;\n  output [519:0] y;\n  assign y = { 256'h" + "f" * 64
                          + ", 256'h0, a };\nendmodule\n", None)
    out["fanout_100"] = (fanout_netlist(100), "n")       # a cell net and an input, each read by 100 gates
    out["fanout_2048"] = (fanout_netlist(2048), "n")
    return out


@needs_lib
class RepairTest(unittest.TestCase):
    """sky130_a0_v2 and v3 (decided 11/04, "add the repair step everywhere (buffering)"): the A0' netlist is repaired by BUFFERING
    ONLY before it is weighed (a balanced buffer tree on every net over its driver's limits, primary inputs, flop Q nets and
    output bits included; the tie cell replicated; nothing resized), the repaired netlist is written, read back, simulated
    against the unrepaired one and weighed; a netlist the repair cannot make legal is REJECTED with the net named."""

    @classmethod
    def setUpClass(cls):
        cls.lib, cls.pins = ppa.open_library()
        cls.dir = tempfile.mkdtemp(prefix="ppa-repair-test-")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    def write(self, name, text):
        p = os.path.join(self.dir, name)
        with open(p, "w") as fh:
            fh.write(text)
        return p

    def test_the_repair_makes_an_illegal_fanout_legal(self):
        text = fanout_netlist()
        with self.assertRaises(ppa.IllegalNetlist) as cm:        # as written (rising edge): inv_1 at 238 fF, the input b's buf_1 at 243 fF
            ppa.analyze(text, self.lib, self.pins, repair_netlist=False, input_drive=BUF1)
        msg = str(cm.exception)
        self.assertIn("2 drivers over max_capacitance", msg)
        self.assertIn("inv_1 _n_ driving net n (100 cell pins): load 237.5 fF, max_capacitance 181.3 fF (1.31x)", msg)
        self.assertIn("buf_1 (input driver) driving net b (100 cell pins): load 242.8 fF, max_capacitance 130.0 fF (1.87x)",
                      msg)
        self.assertNotIn("max_transition", msg)       # the transitions of nets whose tables were left are not known
        self.assertEqual(cm.exception.summary["cells_outside_tables"], 102)   # the 100 readers of b too (its buf_1 slew is off the grid)
        a = ppa.analyze(text, self.lib, self.pins, input_drive=BUF1)    # repaired: buffered, legal, weighed
        s = a.audit.summary()
        self.assertEqual((s["over_max_capacitance"], s["over_max_transition"], s["table_reads_outside"]), (0, 0, 0))
        self.assertLess(s["worst_load_ratio"], 1.0)
        self.assertEqual((a.repair["nets"], a.hist), (2, {"buf_2": 2, "inv_1": 1, "nand2_1": 100}))
        self.assertEqual((a.scored_gates, a.unit_depth), (101, 2))   # the unit depth and gate count are the scored netlist's
        c = ppa.columns(a, self.pins, self.lib, "x")
        self.assertEqual((c["repair"]["cells_before"], c["repair"]["buffers"], c["repair"]["nets_buffered"]), (101, 2, 2))
        self.assertEqual(c["cells_sky130"], sum(c["cell_hist_sky130"].values()))
        self.assertEqual(c["area_e4um2_sky130"], 100 * 37536 + 37536 + 2 * 50048)        # the scored cells + two buf_2

    def test_every_shape_the_review_found_is_buffered_and_legal(self):
        """The loads an `abc` repair never saw (an input or a flop Q wired to output bits or D pins, sign extension, a
        replicated cell net, constants on hundreds of output bits) and plain high fan-out: each ILLEGAL as written (so the
        test is not vacuous), each LEGAL after the repair and weighed, the tree visible in the repaired netlist (the net
        drives buffers only and the buffers its loads; constants: several tie cells, each within its max_capacitance), and
        the repaired netlist computing what the scored one does (the 2048-vector harness, here run again explicitly). The
        inputs are driven by buf_1, the weakest allowed input drive (under the default buf_8 an input carries up to 973 fF:
        `test_the_input_budget_is_the_task_s_drive`)."""
        for name, (text, root) in shapes().items():
            with self.subTest(shape=name):
                with self.assertRaises(ppa.IllegalNetlist):
                    ppa.analyze(text, self.lib, self.pins, repair_netlist=False, input_drive=BUF1)
                a = ppa.analyze(text, self.lib, self.pins, input_drive=BUF1)
                s = a.audit.summary()
                self.assertEqual((s["over_max_capacitance"], s["over_max_transition"], s["cells_outside_tables"]), (0, 0, 0))
                self.assertLessEqual(s["worst_load_ratio"], 1.0)
                rep = ppa.parse_netlist(a.repair["text"])
                bufs = [g for g in rep.gates if re.fullmatch(PREFIX + r"buf_\d+", g.kind)]
                ties = [g for g in rep.gates if g.kind == PREFIX + "conb_1"]
                self.assertEqual((len(bufs), len(ties)), (a.repair["buffers"], a.ties))
                if root is None:
                    self.assertGreater(a.ties, 1)
                    self.assertEqual(a.hist["conb_1"], a.ties)
                else:
                    self.assertGreater(len(bufs), 0)
                    tops = [g for g in bufs if rep.resolve(g.pins["A"]) == root]
                    self.assertTrue(tops)
                    readers = [p for g in rep.gates for p, n in g.pins.items() if rep.resolve(n) == root
                               and not g.kind.startswith(PREFIX + "buf_") and p not in ("Y", "X", "Q", "CLK")]
                    bits = [p for p, _, n in rep.po if rep.resolve(n) == root]
                    self.assertEqual((readers, bits), ([], []), "the repaired net still drives loads directly")
                # the explicit equivalence: the scored netlist and the repaired one on the pinned sample
                raw = ppa.parse_netlist(text)
                flops = [g for g in raw.gates if g.kind == ppa.FLOP_KIND]
                raw.gates = [g for g in raw.gates if g.kind != ppa.FLOP_KIND]
                nl = ppa.expand_a0(raw, self.pins)
                _, dn = ppa.cut_flops(nl, flops)
                ppa.check_repair(ppa.Design(nl, self.lib, self.pins), dn, a.design, a.dn, self.pins)

    def test_the_input_budget_is_the_task_s_drive(self):
        """sky130_a0_v3: the input b read by k inv_1 (each 2.39 fF on a rising edge, 2.214 fF on a falling one; the repair
        counts a pin at its larger edge). The repair holds an input net to its INPUT DRIVE's budget (the load at which that
        cell's output transition reaches 1.5 ns at the pinned 50 ps ramp): buf_8, the default, 973.2 fF, so 407 readers are
        weighed as written and 408 get a tree; buf_1 129.6 fF, 54 and 55. The record's `setup` names the drive."""
        def inv_fan(k):
            return netlist("".join(gate("NOT", f"_g{i}_", A="b", Y=f"y[{i}]") for i in range(k)),
                           ports=f"input b;\n  output [{k - 1}:0] y;")
        for drive, budget, most in ((None, 973.2, 407), (BUF1, 129.6, 54)):
            name = drive or self.pins.input_drive_default
            bud = ppa.Budgets(self.lib, self.pins, ppa.input_drive_cell(self.lib, self.pins, name), None).pi()
            self.assertEqual((round(bud * 1000, 1), int(bud / 0.00239)), (budget, most), name)
            a = ppa.analyze(inv_fan(most), self.lib, self.pins, input_drive=drive)
            self.assertEqual((a.repair["buffers"], a.input_drive), (0, name))
            b = ppa.analyze(inv_fan(most + 1), self.lib, self.pins, input_drive=drive)
            rep = ppa.parse_netlist(b.repair["text"])
            self.assertEqual(b.repair["nets"], 1)
            self.assertTrue([g for g in rep.gates if g.kind.startswith(PREFIX + "buf_") and rep.resolve(g.pins["A"]) == "b"])
            self.assertEqual(ppa.columns(b, self.pins, self.lib, "x")["setup"]["input_drive"], name)

    def test_every_allowed_input_drive_weighs_and_an_unknown_one_is_a_task_error(self):
        """Each cell of the pins' allowlist (buffers, inverters, the flop's Q) drives the input of a netlist whose input
        carries 119.5 fF on a rising edge, 110.7 fF on a falling one (50 inv_1, within even buf_1's budget): legal, weighed,
        recorded. At that load the stronger buffer is the earlier (buf_1 1,231 ps, buf_2 648, buf_8 318), the flop's Q the
        latest (1,259: its clock-to-Q); at a
        light load a big buffer is the slower (its own intrinsic delay). A name outside the allowlist, or a task.json
        `input_drive` naming one, is TaskConfigError."""
        text = netlist("".join(gate("NOT", f"_g{i}_", A="b", Y=f"y[{i}]") for i in range(50)),
                       ports="input b;\n  output [49:0] y;")
        self.assertEqual(self.pins.input_drives, [PREFIX + f"{k}_{n}" for k in ("buf", "inv") for n in (1, 2, 4, 6, 8, 12, 16)]
                         + [PREFIX + "dfxtp_1"])
        t = {}
        for name in self.pins.input_drives:
            a = ppa.analyze(text, self.lib, self.pins, input_drive=name)
            self.assertEqual((a.input_drive, a.audit.summary()["over_max_transition"], a.repair["buffers"]), (name, 0, 0))
            t[name[len(PREFIX):]] = round(a.t_ns * 1000)
        self.assertEqual((t["buf_1"], t["buf_2"], t["buf_8"], t["inv_8"], t["dfxtp_1"]), (1231, 648, 318, 263, 1259))
        self.assertEqual(ppa.input_drive_of(None, self.pins), PREFIX + "buf_8")
        self.assertEqual(ppa.input_drive_of({"name": "x"}, self.pins), PREFIX + "buf_8")
        self.assertEqual(ppa.input_drive_of({"name": "x", "input_drive": BUF1}, self.pins), BUF1)
        for bad in ("buf_8", PREFIX + "buf_3", PREFIX + "clkbuf_1", PREFIX + "nand2_1", None, 8):
            with self.assertRaises(ppa.TaskConfigError):
                ppa.input_drive_of({"name": "x", "input_drive": bad}, self.pins)
            if bad is not None:                                   # None: the default
                with self.assertRaises(ppa.TaskConfigError):
                    ppa.analyze(text, self.lib, self.pins, input_drive=bad)
        with open(ppa.PINS_PATH) as fh:
            raw = json.load(fh)
        for allowed, default in (([BUF1, PREFIX + "nand2_1"], BUF1), ([BUF1], PREFIX + "buf_8"), ([BUF1, BUF1], BUF1),
                                 (["buf_1"], "buf_1"), ([], BUF1)):
            bad = json.loads(json.dumps(raw))
            bad["timing"]["input_drive"] = {"allowed": allowed, "default": default}
            with self.assertRaises(ppa.PpaError) as cm:
                ppa.Pins(self.write("bad_drive.json", json.dumps(bad)))
            self.assertIn("timing.input_drive.allowed", str(cm.exception))

    def test_the_tie_cell_is_audited_and_replicated(self):
        """The hole of the ABC repair: one conb_1 for 255 constant-0 output bits (2.55 pF on LO, max_capacitance 2.05 pF) was
        weighed as legal. As written it is now ILLEGAL (the tie cell's load is audited); repaired, two conb_1 share the
        bits (127 + 128, in bit order: the balanced cut nearest half the load)."""
        text = shapes()["const_256_bits"][0]
        with self.assertRaises(ppa.IllegalNetlist) as cm:
            ppa.analyze(text, self.lib, self.pins, repair_netlist=False)
        self.assertIn("tie cell conb_1 LO driving constant 0 (255 output bits (y[1] .. y[255])): load 2550.0 fF, "
                      "max_capacitance 2046.8 fF (1.25x)", str(cm.exception))
        a = ppa.analyze(text, self.lib, self.pins)
        self.assertEqual((a.ties, a.hist, a.area_e4, a.cells), (2, {"conb_1": 2}, 2 * 37536, 2))
        rep = ppa.parse_netlist(a.repair["text"])
        lo = [g.pins["LO"] for g in rep.gates]
        self.assertEqual([sum(1 for _, _, n in rep.po if rep.resolve(n) == x) for x in lo], [127, 128])

    def test_the_tree_is_balanced_and_the_cheapest_level(self):
        """2048 nand2 gates read one inverter (A: 2.375 fF each at its larger edge, rise_capacitance, 4.86 pF) and one input
        (B: 2.428 fF each). The level of least area over the pins' buffers within their budgets is 9 x buf_4 (556.6 fF each:
        67.6 um^2; 16 x buf_2 = 80.1, 7 x buf_6 = 78.8, 6 x buf_8 = 90.1, ...), the 2048 loads split 228/227 in instance
        order; the driver then carries 9 buf_4 inputs (22.7 fF), one level. The budgets are the liberty's: the load at which
        the output transition reaches 1.5 ns at a 1.5 ns input, within max_capacitance."""
        a = ppa.analyze(fanout_netlist(2048), self.lib, self.pins)
        self.assertEqual((a.hist, a.repair["nets"]), ({"buf_4": 18, "inv_1": 1, "nand2_1": 2048}, 2))
        rep = ppa.parse_netlist(a.repair["text"])
        for root, pin in (("n", "A"), ("b", "B")):
            tree = [g for g in rep.gates if g.kind.startswith(PREFIX + "buf_") and rep.resolve(g.pins["A"]) == root]
            sizes = [sum(1 for h in rep.gates for p, n in h.pins.items() if p == pin and n == g.pins["X"]) for g in tree]
            self.assertEqual(sizes, [228, 227] * 4 + [228])
            first = [int(h.inst[2:-1]) for h in rep.gates if h.pins.get(pin) == tree[0].pins["X"]]
            self.assertEqual(first, list(range(228)))            # the first group is the first 228 gates, in natural order
        bud = ppa.Budgets(self.lib, self.pins, self.lib.cell(PREFIX + "buf_1"), None)
        self.assertEqual([(b[1], round(b[3] * 1000, 1)) for b in bud.buffers],
                         [("buf_1", 129.5), ("buf_2", 313.7), ("buf_4", 556.6), ("buf_6", 783.6), ("buf_8", 968.2),
                          ("buf_12", 1372.4), ("buf_16", 1482.9)])

    def test_the_repaired_netlist_is_verilog_that_yosys_reads(self):
        """The repaired netlist is the weighed one (its sha256 in the record), structural Verilog over the liberty's cells:
        Yosys reads it against the liberty (cells as black boxes) and finds the module, its cells and its buffers."""
        import score
        y = shutil.which(score.yosys_bin())
        if y is None:                                     # pragma: no cover
            self.skipTest("no Yosys")
        text = shapes()["q_to_17_bits"][0]
        a = ppa.analyze(text, self.lib, self.pins)
        c = ppa.columns(a, self.pins, self.lib, "x")
        self.assertEqual(c["repair"]["netlist_sha256"], ppa.sha256_bytes(a.repair["text"].encode()))
        v = self.write("rep.v", a.repair["text"])
        r = subprocess.run([y, "-q", "-p", f"read_liberty -lib {REAL_LIB}; read_verilog {v}; hierarchy -top t; stat"],
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout[-2000:] + r.stderr[-2000:])

    def test_two_clean_runs_are_byte_identical(self):
        """The CLI in separate processes (other hash seeds, other temp directories): the same record and the same repaired
        netlist, byte for byte; a clocked netlist (a flop's Q read by 80 gates: 192 fF at the pins' larger edge, over the Q's
        162 fF budget, while the input a's 194 fF is within buf_8's) and constants too. (sky130_a0_v2's version read the Q by 60 gates, 141 fF,
        within the Q's budget: its one buffer was the input a's, over buf_1's 130 fF.)"""
        clocked = netlist(gate("NOT", "_1_", A="q", Y="d") + gate("DFF_P", "_2_", C="c", D="d", Q="q")
                          + "".join(gate("NAND", f"_g{i}_", A="q", B="a", Y=f"y[{i}]") for i in range(80)),
                          ports="input a;\n  input c;\n  output [79:0] y;", wires="wire d;\n  wire q;")
        for name, text in (("fan.v", fanout_netlist()), ("clk.v", clocked), ("cst.v", shapes()["const_hi_lo"][0])):
            net = self.write(name, text)
            outs, reps = [], []
            for seed in ("0", "77"):
                with tempfile.TemporaryDirectory() as t:
                    rep = os.path.join(t, "rep.v")
                    env = dict(os.environ, PYTHONHASHSEED=seed, PYTHONDONTWRITEBYTECODE="1", TMPDIR=t)
                    r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), "--netlist-in", net, "--path",
                                        "--repaired-netlist", rep], capture_output=True, text=True, env=env)
                    self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                    outs.append(r.stdout)
                    with open(rep, "rb") as fh:
                        reps.append(fh.read())
            self.assertEqual(outs[0], outs[1], name)
            self.assertEqual(reps[0], reps[1], name)
            p = json.loads(outs[0])["ppa"]
            self.assertEqual(p["repair"]["netlist_sha256"], ppa.sha256_bytes(reps[0]))
            if name == "clk.v":
                self.assertEqual((p["sequential"], p["flops"], p["repair"]["buffers"]), (True, 1, 1))   # Q buffered
                self.assertIn("the net q (the Q of flop _2_)", reps[0].decode())     # the tree's comment names the Q net

    def test_constants_on_cell_pins_go_through_the_repair(self):
        """A constant on a cell pin: the repaired netlist ties it to a conb_1 output, read back as the constant."""
        a = ppa.analyze(netlist(gate("NAND", "_1_", A="a", B="1'h1", Y="y")), self.lib, self.pins)
        self.assertTrue(a.constants)
        self.assertEqual(a.hist, {"conb_1": 1, "nand2_1": 1})
        self.assertEqual(a.design.ins[0]["B"], "1")
        self.assertIn(PREFIX + "conb_1", a.repair["text"])

    def test_a_repair_that_changes_the_function_is_a_defect_not_a_number(self):
        real = ppa.Repair.write

        def swapped(self_, *a, **kw):
            out = real(self_, *a, **kw)
            return out.replace(PREFIX + "nand2_1", PREFIX + "nor2_1")
        with mock.patch.object(ppa.Repair, "write", swapped):
            with self.assertRaises(ppa.RepairDefect) as cm:
                ppa.analyze(fanout_netlist(20), self.lib, self.pins)
        self.assertIn("differs from the A0' netlist at output y[0]", str(cm.exception))

    def test_the_pinned_repair(self):
        self.assertEqual((self.pins.repair_method, self.pins.repair_buffers, self.pins.repair_max_rounds,
                          self.pins.input_drive_default, self.pins.tie_cell, self.pins.tie_policy),
                         ("buffer_trees_v1", ["buf_1", "buf_2", "buf_4", "buf_6", "buf_8", "buf_12", "buf_16"], 32,
                          PREFIX + "buf_8", "conb_1", "replicated_within_max_capacitance"))
        with open(ppa.PINS_PATH) as fh:
            raw = json.load(fh)
        self.assertNotIn("abc", json.dumps(raw["repair"]).lower().replace("abc -g", ""))    # no ABC in the ranked repair
        for key, val, why in (("method", "abc_sizing", "is not this ppa.py's"), ("buffers", [], "at least one buffer")):
            bad = json.loads(json.dumps(raw))
            bad["repair"][key] = val
            with self.assertRaises(ppa.PpaError) as cm:
                ppa.Pins(self.write("bad_pins.json", json.dumps(bad)))
            self.assertIn(why, str(cm.exception))
        bad = json.loads(json.dumps(raw))
        bad["repair"]["buffers"] = ["buf_1", "inv_1"]             # not a buffer
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze(fanout_netlist(), self.lib, ppa.Pins(self.write("bad_pins.json", json.dumps(bad))))
        self.assertIn("inv_1, which is not a one-input, one-output logic buffer", str(cm.exception))


def review_probes():
    """The adversarial RTL of the 11/04 review of the ABC-sizing repair, {name: (flow, SystemVerilog)}, top `t`: an input, a
    flop's Q, a cell net or a constant wired to many output bits or D pins, wide fan-out and fan-in, a heavy chain."""
    P = {}
    for k in (13, 14):
        P[f"pi_po_{k}"] = ("comb", f"module t(input a, input b, output [{k - 1}:0] y, output z); assign y = {{{k}{{a}}}}; "
                                   "assign z = ~b; endmodule\n")
    P["signext_16_32"] = ("comb", "module t(input [15:0] x, output [31:0] y); assign y = {{16{x[15]}}, x}; endmodule\n")
    P["mask_lt_32"] = ("comb", "module t(input [7:0] a, input [7:0] b, output [31:0] y); assign y = {32{a < b}}; endmodule\n")
    P["mask_and_20"] = ("comb", "module t(input a, input b, output [19:0] y); assign y = {20{a & b}}; endmodule\n")
    P["const_po_256"] = ("comb", "module t(input a, output [255:0] y); assign y = {255'b0, a}; endmodule\n")
    P["const_po_1024"] = ("comb", "module t(input a, output [1023:0] y); assign y = {1023'b0, a}; endmodule\n")
    P["const1_po_200"] = ("comb", "module t(input a, output [200:0] y); assign y = {{200{1'b1}}, a}; endmodule\n")
    P["const_mix_hi_lo"] = ("comb", "module t(input [7:0] a, output [519:0] y); assign y = {{256{1'b1}}, {256{1'b0}}, a}; "
                                    "endmodule\n")
    P["fan_pi_2048"] = ("comb", "module t(input a, input [2047:0] b, output [2047:0] y); assign y = b & {2048{a}}; "
                                "endmodule\n")
    P["fan_pi_mux_512"] = ("comb", "module t(input s, input [511:0] b, input [511:0] c, output [511:0] y); "
                                   "assign y = s ? b : c; endmodule\n")
    P["wide_and_4096"] = ("comb", "module t(input [4095:0] b, output y); assign y = &b; endmodule\n")
    P["wide_xor_4096"] = ("comb", "module t(input [4095:0] b, output y); assign y = ^b; endmodule\n")
    P["chain_heavy"] = ("comb", "module t(input [63:0] a, input [767:0] b, output [767:0] y, output z);\n"
                                "  wire [64:0] c; assign c[0] = a[0];\n  genvar i; generate for (i = 0; i < 64; i = i + 1) "
                                "begin : g\n    assign c[i+1] = c[i] ^ a[i];\n    assign y[i*12 +: 12] = b[i*12 +: 12] ^ "
                                "{12{c[i+1]}};\n  end endgenerate\n  assign z = c[64];\nendmodule\n")
    for k in (64, 128):
        P[f"q_to_d_{k}"] = ("seq", f"module t(input clk, input a, output [{k - 1}:0] y);\n  reg r0; reg [{k - 1}:0] r;\n"
                                   f"  always @(posedge clk) begin r0 <= a; r <= {{{k}{{r0}}}}; end\n  assign y = r;\nendmodule\n")
    for k in (15, 17):
        P[f"q_to_po_{k}"] = ("seq", f"module t(input clk, input a, output [{k - 1}:0] y);\n  reg r0; always @(posedge clk) "
                                    f"r0 <= a; assign y = {{{k}{{r0}}}};\nendmodule\n")
    P["q_fan_1024"] = ("seq", "module t(input clk, input e, input [1023:0] d, output [1023:0] y);\n  reg en; reg [1023:0] r;\n"
                              "  always @(posedge clk) begin en <= e; r <= en ? d : r; end\n  assign y = r;\nendmodule\n")
    P["pi_to_d_96"] = ("seq", "module t(input clk, input a, output [95:0] y);\n  reg [95:0] r; always @(posedge clk) "
                              "r <= {96{a}}; assign y = r;\nendmodule\n")
    P["clk_as_data"] = ("seq", "module t(input clk, input [19:0] a, output [19:0] y);\n  reg [19:0] r; always @(posedge clk) "
                               "r <= a; assign y = r & {20{clk}};\nendmodule\n")
    for k in (24, 32, 48):
        P[f"offcrit_rep_{k}"] = ("comb", f"module t(input [63:0] p, input [63:0] q, input a, input b, output [63:0] s, "
                                         f"output [{k - 1}:0] y);\n  wire [64:0] c; assign c[0] = 1'b0;\n  genvar i; generate "
                                         "for (i = 0; i < 64; i = i + 1) begin : g\n    assign s[i] = p[i] ^ q[i] ^ c[i];\n"
                                         "    assign c[i+1] = (p[i] & q[i]) | (c[i] & (p[i] ^ q[i]));\n  end endgenerate\n"
                                         f"  assign y = {{{k}{{a & b}}}};\nendmodule\n")
    return P


@needs_flow
class ReviewProbesTest(unittest.TestCase):
    """Every probe of the 11/04 review through the pinned flow and the ranked weighing: each LEGAL and scored. The nine the
    ABC-sizing repair REJECTED (loads it never saw: an input or a flop's Q to output bits or D pins, a replicated cell net
    off the critical path) now carry a buffer tree; the four with hundreds of constant output bits, which it scored with ONE
    overloaded tie cell, carry several. The probes were built for buf_1 driving the inputs (sky130_a0_v2): they are weighed
    under it (a task may choose it; the weakest allowed buffer) and under the default buf_8, legal both times; under buf_8
    an input to 14 or 17 output bits is within its limits and needs no tree."""
    REJECTED_BY_ABC = ("pi_po_14", "signext_16_32", "q_to_d_64", "q_to_d_128", "q_to_po_17", "pi_to_d_96", "offcrit_rep_24",
                       "offcrit_rep_32", "offcrit_rep_48")
    CONSTANTS = ("const_po_256", "const_po_1024", "const1_po_200", "const_mix_hi_lo")

    def test_every_probe_is_legal_and_scored(self):
        d = tempfile.mkdtemp(prefix="ppa-probes-")
        try:
            for name, (flow, sv) in review_probes().items():
                with self.subTest(probe=name):
                    src = os.path.join(d, name + ".sv")
                    with open(src, "w") as fh:
                        fh.write(sv)
                    p = ppa.score_and_weigh([src], "t", {}, mapped=False, flow=flow, input_drive=BUF1)["ppa"]
                    p8 = ppa.score_and_weigh([src], "t", {}, mapped=False, flow=flow)["ppa"]
                    for q in (p, p8):
                        lg = q["legality"]
                        self.assertEqual((lg["over_max_capacitance"], lg["over_max_transition"], lg["table_reads_outside"]),
                                         (0, 0, 0))
                        self.assertGreater(q["delay_ps_sky130"], 0)
                    self.assertEqual((p["setup"]["input_drive"], p8["setup"]["input_drive"]), (BUF1, PREFIX + "buf_8"))
                    if name in self.REJECTED_BY_ABC:
                        self.assertGreater(p["repair"]["buffers"], 0)
                    if name in self.CONSTANTS:
                        self.assertGreater(p["repair"]["tie_cells"], 1)
                        self.assertEqual(p["cell_hist_sky130"]["conb_1"], p["repair"]["tie_cells"])
        finally:
            shutil.rmtree(d, ignore_errors=True)


class UnfixableTest(unittest.TestCase):
    """What the repair cannot make legal is REJECTED, the net named in the design's words, on synthetic liberties built to
    have such a net: a cell that cannot drive anything within its max_transition, an input ramp below a table's grid."""

    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="ppa-unfixable-test-")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    def lib(self, text):
        p = os.path.join(self.dir, "u.lib")
        with open(p, "w") as fh:
            fh.write(text)
        pins = write_pins(os.path.join(self.dir, "u.json"), p)
        return ppa.Liberty(p, pins), pins

    def test_a_cell_too_weak_for_any_load_is_rejected_naming_it(self):
        """inv_1's output transition is at least 15 ps at any load; a max_transition of 10 ps on its Y: no buffer tree can
        help (its driver could carry no load at all)."""
        lib, pins = self.lib(mini_lib().replace('function : "(!A)";', 'function : "(!A)"; max_transition : 0.010;'))
        with self.assertRaises(ppa.IllegalNetlist) as cm:
            ppa.analyze(TINY, lib, pins)
        msg = str(cm.exception)
        self.assertIn("the repair (buffer trees, replicated tie cells) cannot make it legal: the net _0_ (inv_1 _1_), "
                      "driving 1 cell pin: its driver may carry at most 0.0 fF, less than the buffers it would need", msg)
        self.assertIn("so the design is rejected", msg)

    def test_an_input_ramp_below_the_grid_is_rejected(self):
        """buf_1's tables start at 60 ps; the pinned input ramp is 50 ps: every input's driver is read below its grid."""
        text = mini_lib()
        k = text.index(f'cell ("{PREFIX}buf_1")')
        lib, pins = self.lib(text[:k] + text[k:].replace('index_1("0.0, 0.1")', 'index_1("0.06, 0.1")'))
        with self.assertRaises(ppa.IllegalNetlist) as cm:
            ppa.analyze(TINY, lib, pins)
        self.assertIn("a timing table is read BELOW its characterized range at net a", str(cm.exception))


@needs_lib
class MappedPoliciesTest(unittest.TestCase):
    """Flow A1' against the real liberty: the pinned script and the cell policy."""

    @classmethod
    def setUpClass(cls):
        cls.pins = REAL_PINS
        cls.lib = ppa.Liberty(REAL_LIB, cls.pins)
        cls.mpins = ppa.MappedPins(cls.pins)
        with open(ppa.MAPPED_SCRIPT_PATH) as fh:
            cls.ys = fh.read()

    def test_the_dont_use_globs_are_exactly_the_policy(self):
        """`abc -dont_use` takes globs; the pinned script's list excludes a cell iff `cell_class` is not `logic` (268 of the 428
        cells stay: the same set ABC reports as its library, `has 268 cells`). One policy, written twice, agreeing on every cell."""
        globs = re.findall(r"-dont_use (\S+)", self.ys)
        self.assertEqual(len(globs), 24)
        self.assertTrue(all(g.startswith(PREFIX) for g in globs))
        allowed = [n for n in self.lib.cell_names if not any(fnmatch.fnmatchcase(n, g) for g in globs)]
        self.assertEqual(len(self.lib.cell_names), 428)
        self.assertEqual(len(allowed), 268)
        self.assertEqual(allowed, [n for n in self.lib.cell_names if ppa.cell_class(n) == "logic"])

    def test_the_script_is_the_pinned_abc_script_and_is_yosys_0_53s_default(self):
        body = [ln for ln in self.ys.splitlines() if ln and not ln.startswith("#")]
        self.assertEqual([ln.split()[0] for ln in body], ["read_rtlil", "synth", "abc", "opt_clean", "write_verilog"])
        m = re.search(r"-script \+(\S+)$", body[2])
        self.assertIsNotNone(m)
        self.assertEqual(" ".join(m.group(1).replace(",", " ").split()), " ".join(self.mpins.abc_script.split()))
        self.assertEqual(self.mpins.abc_script, "strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; "
                                                "&dch -f; &nf; &put")
        for banned in ("-constr", " -D ", "hilomap", "-fast", "buffer", "upsize"):     # no sizing pass, no delay target, no tie cells
            self.assertNotIn(banned, "\n".join(body), banned)

    def test_the_pins_are_for_the_same_liberty_and_the_pins_file_is_untouched_a0(self):
        self.assertEqual(self.mpins.lib_sha256, self.pins.lib["sha256"])
        # A0''s identity does not depend on flow A1': ppa_pins.json has no mapped-flow content
        with open(ppa.PINS_PATH) as fh:
            raw = json.load(fh)
        self.assertEqual(raw["ppa_version"], "sky130_a0_v3")
        self.assertNotIn("mapped", json.dumps(raw))


@needs_flow
class FlowTest(unittest.TestCase):
    """The pinned flow of score.py, then the columns, on the reference designs: golden values and consistency."""

    @classmethod
    def setUpClass(cls):
        with open(os.path.join(HERE, "tests", "ppa", "expected_ppa.json")) as fh:
            cls.gold = json.load(fh)
        cls.designs = ppa_validate.load_designs()

    def test_golden_columns_of_every_reference(self):
        self.assertEqual(self.gold["liberty_sha256"], REAL_PINS.lib["sha256"])
        self.assertEqual(self.gold["ppa_version"], REAL_PINS.version)
        self.assertEqual(sorted(self.gold["designs"]), sorted(d["name"] for d in self.designs))
        for d in self.designs:
            with self.subTest(design=d["name"]):
                r = ppa_validate.measure(d, mapped=True)       # flow A1' rides along: one scoring per design (WP-X4)
                g = self.gold["designs"][d["name"]]
                for k in ("area_ge", "depth", "gates", "cells", "area_e4um2", "delay_ps", "unit_depth", "repaired_sha256"):
                    self.assertEqual(r[k], g[k], k)
                self.assertEqual(r["unit_depth"], r["depth"])          # the scored netlist's depth is ltp's
                self.assertEqual(r["cells_before"], r["gates"])        # and its cells (before the repair) the gates
                self.assertLess(r["worst_load_ratio"], 1.0)             # legal (else it would have raised)
                self.assertNotIn("m_error", r)
                mg = self.mapped_gold()["designs"][d["name"]]
                self.assertEqual({"rtlil_sha256": r["rtlil_sha256"], "area_e4um2": r["m_area_e4um2"],
                                  "delay_ps": r["m_delay_ps"], "cells": r["m_cells"], "levels": r["m_levels"],
                                  "buffers": r["m_buffers"], "inverters": r["m_inverters"], "constants": r["m_constants"],
                                  "netlist_sha256": r["m_netlist_sha256"]}, mg)
                self.assertEqual(r["rtlil_sha256"], g["rtlil_sha256"])      # the mapping read the circuit the A0' golden is of

    def test_netlist_idioms_with_dead_public_wires(self):
        """Designs whose scored netlist carries the dead public-named wires of techmapped cells (a run-time bit select, a
        variable shift, a case mux, a constant table, a one-hot decode, a packed-array index, a divider): the reader once
        refused every one of them (`assign width mismatch`). Golden columns, as for the references; and the netlists really
        contain the escaped wires the test is about (a Yosys that stopped leaving them would make this test vacuous)."""
        import score
        with open(os.path.join(HERE, "tests", "ppa", "expected_idioms.json")) as fh:
            gold = json.load(fh)
        self.assertEqual(gold["liberty_sha256"], REAL_PINS.lib["sha256"])
        self.assertEqual(gold["ppa_version"], REAL_PINS.version)
        idioms = ppa_validate.load_designs(path="idioms.json")
        self.assertEqual(sorted(gold["designs"]), sorted(d["name"] for d in idioms))
        escaped = re.compile(r"^\s*wire\b[^;\n]*\\\S+ ;", re.M)
        with_dead_wires = 0
        for d in idioms:
            with self.subTest(design=d["name"]):
                with tempfile.TemporaryDirectory() as tmp:
                    net, il = os.path.join(tmp, "n.v"), os.path.join(tmp, "c.il")
                    sres = score.score([os.path.join(SVGOLF, d["src"])], d["top"], d["params"], netlist_out=net, rtlil_out=il)
                    with open(net) as fh:
                        with_dead_wires += bool(escaped.search(fh.read()))
                    cols = ppa.weigh_netlist_file(net)
                    mapped = ppa.mapped_block(il, d["top"], open(net).read(), *ppa.open_library())
                g = gold["designs"][d["name"]]
                self.assertEqual((sres["area_ge"], sres["depth"], sres["num_gates"]), (g["area_ge"], g["depth"], g["gates"]))
                for k, gk in (("area_e4um2_sky130", "area_e4um2"), ("delay_ps_sky130", "delay_ps"),
                              ("unit_depth", "unit_depth"), ("cells_sky130", "cells"), ("netlist_sha256", "netlist_sha256")):
                    self.assertEqual(cols[k], g[gk], k)
                self.assertEqual(cols["repair"]["netlist_sha256"], g["repaired_sha256"])
                self.assertEqual(cols["unit_depth"], sres["depth"])
                self.assertEqual(cols["repair"]["cells_before"], sres["num_gates"])
                # flow A1' on the same circuits: the golden mapped columns (the dead wires of the scored netlist
                # are not in the RTLIL's mapping at all)
                mg = self.mapped_gold()["designs"][d["name"]]
                self.assertTrue(mapped["available"], mapped)
                self.assertEqual({"rtlil_sha256": mapped["rtlil_sha256"], "area_e4um2": mapped["area_e4um2_sky130_mapped_v1"],
                                  "delay_ps": mapped["mapped_delay_sky130_v1"], "cells": mapped["mapped_cells_sky130_v1"],
                                  "levels": mapped["mapped_levels_sky130_v1"], "buffers": mapped["mapped_buffers_sky130_v1"],
                                  "inverters": mapped["mapped_inverters_sky130_v1"], "constants": mapped["constants"],
                                  "netlist_sha256": mapped["netlist_sha256"]}, mg)
                self.assertEqual(mapped["rtlil_sha256"], sres["rtlil_sha256"])
        self.assertGreaterEqual(with_dead_wires, len(idioms) - 1, "the idioms no longer leave escaped wires in the netlist")

    def test_default_score_is_untouched(self):
        """score_and_weigh returns score.py's result unchanged: (area_ge_v1, depth_v1) stay the board."""
        import score
        d = ppa_validate.load_designs(["add_ripple"])[0]
        src = [os.path.join(SVGOLF, d["src"])]
        both = ppa.score_and_weigh(src, d["top"], d["params"])
        self.assertEqual(both["score"], score.score(src, d["top"], d["params"]))
        self.assertEqual((both["score"]["area_ge"], both["score"]["depth"]), (112.0, 33))
        self.assertEqual((both["ppa"]["area_um2_sky130"], both["ppa"]["delay_ps_sky130"]), (460.4416, 2611))

    def test_cli_task_flag_is_deterministic_across_processes(self):
        cmd = [sys.executable, os.path.join(HERE, "ppa.py"), os.path.join(SVGOLF, "tasks", "add", "reference", "add_n.sv"),
               "--task", os.path.join(SVGOLF, "tasks", "add")]
        outs = []
        for seed in ("1", "2"):
            env = dict(os.environ, PYTHONHASHSEED=seed, PYTHONDONTWRITEBYTECODE="1")
            r = subprocess.run(cmd, capture_output=True, text=True, env=env)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            outs.append(r.stdout)
        self.assertEqual(outs[0], outs[1])
        res = json.loads(outs[0])
        self.assertEqual(res["ppa"]["delay_ps_sky130"], 2611)
        self.assertEqual(res["ppa"]["setup"]["input_drive"], PREFIX + "buf_8")       # the add task declares none: the default
        self.assertEqual(res["score"]["params"], {"N": 16})

    def test_the_task_s_input_drive_is_the_one_weighed(self):
        """sky130_a0_v3: `--task` reads task.json's `input_drive` (here a copy of the add task declaring buf_1, sky130_a0_v2's
        drive, which gives the ripple adder 2627 ps), records it in `setup`, and `--input-drive` may not contradict it; a cell
        outside the pins' allowlist is a task-configuration error (exit 1), never a number."""
        with open(os.path.join(SVGOLF, "tasks", "add", "task.json")) as fh:
            task = json.load(fh)
        sv = os.path.join(SVGOLF, "tasks", "add", "reference", "add_n.sv")
        with tempfile.TemporaryDirectory() as tmp:
            def run(drive, *more):
                with open(os.path.join(tmp, "task.json"), "w") as fh:
                    json.dump(dict(task, input_drive=drive), fh)
                return subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), sv, "--task", tmp, "--no-mapped", *more],
                                      capture_output=True, text=True)
            r = run(BUF1)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            p = json.loads(r.stdout)["ppa"]
            self.assertEqual((p["delay_ps_sky130"], p["area_um2_sky130"], p["setup"]["input_drive"]), (2627, 460.4416, BUF1))
            r = run(BUF1, "--input-drive", PREFIX + "buf_8")
            self.assertEqual(r.returncode, 2)
            self.assertIn("contradicts the task's input_drive", r.stderr)
            r = run(PREFIX + "buf_3")
            self.assertEqual(r.returncode, 1)
            self.assertIn("task add: input_drive 'sky130_fd_sc_hd__buf_3' is not one of the allowed input drives",
                          json.loads(r.stdout)["error"])

    def test_netlist_in_agrees_with_the_design_path(self):
        import score
        d = ppa_validate.load_designs(["sbox_table"])[0]
        with tempfile.TemporaryDirectory() as tmp:
            net = os.path.join(tmp, "n.v")
            both = ppa.score_and_weigh([os.path.join(SVGOLF, d["src"])], d["top"], d["params"], netlist_out=net)
            again = ppa.weigh_netlist_file(net)
        self.assertEqual({k: v for k, v in both["ppa"].items() if k != "mapped"}, again)        # A0' is the same either way
        self.assertTrue(both["ppa"]["mapped"]["available"])
        self.assertEqual(both["ppa"], dict(ppa.score_and_weigh([os.path.join(SVGOLF, d["src"])], d["top"], d["params"])["ppa"]))

    # ---- flow A1' (WP-X4)
    @classmethod
    def mapped_gold(cls):
        with open(os.path.join(HERE, "tests", "ppa", "expected_ppa_mapped.json")) as fh:
            return json.load(fh)

    def test_the_mapped_goldens_are_for_the_pinned_inputs(self):
        """expected_ppa_mapped.json (every design of designs.json and idioms.json; compared per design in the golden tests above
        and below, one scoring each) was recorded under the pinned script, liberty, Yosys and ABC builds and names exactly those
        designs (`ppa_validate.py table --designs designs.json,idioms.json --mapped-expected-out ...`)."""
        import score
        gold = self.mapped_gold()
        mp = ppa.MappedPins(REAL_PINS)
        self.assertEqual((gold["ppa_mapped_version"], gold["liberty_sha256"], gold["ppa_mapped_script_sha256"]),
                         (mp.version, REAL_PINS.lib["sha256"], mp.script_sha256))
        self.assertEqual((gold["yosys_version"], gold["abc_version"]), (mp.yosys_version, mp.abc_version))
        self.assertEqual((score.yosys_version(score.yosys_bin()), ppa.abc_version(score.yosys_bin())),
                         (mp.yosys_version, mp.abc_version), "the Yosys/ABC build is not the one the goldens were recorded with")
        designs = ppa_validate.load_designs() + ppa_validate.load_designs(path="idioms.json")
        self.assertEqual(sorted(gold["designs"]), sorted(d["name"] for d in designs))

    def test_the_default_columns_are_the_same_with_and_without_the_mapping(self):
        """A0' does not depend on A1': `ppa` minus `mapped` is what `--no-mapped` (and the previous version) gives."""
        d = ppa_validate.load_designs(["add_kogge"])[0]
        src = [os.path.join(SVGOLF, d["src"])]
        both = ppa.score_and_weigh(src, d["top"], d["params"])
        a0 = ppa.score_and_weigh(src, d["top"], d["params"], mapped=False)
        self.assertNotIn("mapped", a0["ppa"])
        self.assertEqual({k: v for k, v in both["ppa"].items() if k != "mapped"}, a0["ppa"])
        self.assertEqual(both["score"], a0["score"])

    def test_the_mapped_flow_is_not_the_scored_netlist_weighed_again(self):
        """The two flows differ on the proved array multiplier (the case the study is about): A0' prices the abstract netlist
        (1408 gates, nothing over a limit so nothing buffered, 8290 um^2), A1' maps it onto compound cells and drive strengths
        (834 cells, 8645 um^2, other levels)."""
        d = ppa_validate.load_designs(["mul_array"])[0]
        r = ppa.score_and_weigh([os.path.join(SVGOLF, d["src"])], d["top"], d["params"])
        p, m = r["ppa"], r["ppa"]["mapped"]
        self.assertEqual((p["repair"]["cells_before"], p["cells_sky130"], p["area_e4um2_sky130"]), (1408, 1408, 82904512))
        self.assertEqual((m["mapped_cells_sky130_v1"], m["area_e4um2_sky130_mapped_v1"]), (834, 86445408))
        self.assertNotEqual(m["netlist_sha256"], p["netlist_sha256"])
        self.assertTrue(any(c.startswith(("maj3", "a21oi", "o21ai", "xnor3")) for c in m["mapped_cell_hist_sky130_v1"]))
        self.assertGreater(m["mapped_buffers_sky130_v1"] + m["mapped_inverters_sky130_v1"], 0)

    def test_constants_in_the_mapped_flow_cost_one_tie_cell_as_in_a0(self):
        with tempfile.TemporaryDirectory() as tmp:
            sv = os.path.join(tmp, "cst.sv")
            with open(sv, "w") as fh:
                fh.write("module cst(input logic [3:0] a, input logic [3:0] b, output logic [7:0] y, output logic z);\n"
                         "  assign y = {4'b1010, a ^ b};\n  assign z = 1'b0;\nendmodule\n")
            r = ppa.score_and_weigh([sv], "cst", {})
        p, m = r["ppa"], r["ppa"]["mapped"]
        self.assertTrue(p["constants"] and m["constants"])
        self.assertEqual(m["mapped_cell_hist_sky130_v1"], {"conb_1": 1, "xor2_1": 4})
        self.assertEqual((m["mapped_cells_sky130_v1"], m["area_e4um2_sky130_mapped_v1"]), (5, 387872))
        self.assertEqual(m["area_e4um2_sky130_mapped_v1"], p["area_e4um2_sky130"])

    def test_a_mapped_netlist_that_computes_something_else_is_refused(self):
        """Real flow, real library: the mapped netlist of add_ripple with every `maj3_1` (the carry) replaced by an `or3_1`
        (same pins, other function) is a MappedDefect, found by the equivalence sample."""
        d = ppa_validate.load_designs(["add_ripple"])[0]
        with tempfile.TemporaryDirectory() as tmp:
            mapped = os.path.join(tmp, "mapped.v")
            sv = [os.path.join(SVGOLF, d["src"])]
            import score
            net, il = os.path.join(tmp, "n.v"), os.path.join(tmp, "c.il")
            score.score(sv, d["top"], d["params"], netlist_out=net, rtlil_out=il)
            lib, pins = ppa.open_library()
            with open(net) as fh:
                scored = fh.read()
            ok = ppa.mapped_block(il, d["top"], scored, lib, pins, netlist_out=mapped)
            self.assertTrue(ok["available"])
            with open(mapped) as fh:
                text = fh.read()
            self.assertIn(PREFIX + "maj3_1", text)
            nl, _ = ppa.analyze_mapped(text.replace(PREFIX + "maj3_1", PREFIX + "or3_1"), lib, pins)   # weighable ...
            with self.assertRaises(ppa.MappedDefect):                                                   # ... but not the circuit
                ppa.check_equivalent(scored, nl, lib, pins, ppa.MappedPins(pins))
            with mock.patch.object(ppa, "map_rtlil", return_value=text.replace(PREFIX + "maj3_1", PREFIX + "or3_1")):
                with self.assertRaises(ppa.MappedDefect):
                    ppa.mapped_block(il, d["top"], scored, lib, pins)

    def test_a_design_the_mapping_cannot_read_has_a_loud_reason_not_a_number(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = os.path.join(tmp, "bad.il")
            with open(bad, "w") as fh:
                fh.write("this is not RTLIL\n")
            lib, pins = ppa.open_library()
            b = ppa.mapped_block(bad, "top", "module tiny(a, y);\nendmodule\n", lib, pins)
        self.assertEqual(set(b), {"available", "reason"})
        self.assertFalse(b["available"])
        self.assertIn("the mapping run failed", b["reason"])
        self.assertNotIn("\n", b["reason"])

    def test_omitting_the_script_gives_the_same_netlist(self):
        """The pinned script is Yosys 0.53's default for `abc -liberty`: the same netlist, byte for byte, without `-script`
        (checked on all 24 designs when the pins were made; one design here, so a Yosys whose default moved is noticed)."""
        d = ppa_validate.load_designs(["add_sklansky"])[0]
        import score
        with tempfile.TemporaryDirectory() as tmp:
            il = os.path.join(tmp, "c.il")
            score.score([os.path.join(SVGOLF, d["src"])], d["top"], d["params"], rtlil_out=il)
            lib, pins = ppa.open_library()
            mp = ppa.MappedPins(pins)
            omit = os.path.join(tmp, "omit.ys")
            with open(ppa.MAPPED_SCRIPT_PATH) as fh:
                lines = [ln.split(" -script ")[0] if ln.startswith("abc -liberty") else ln for ln in fh.read().splitlines()]
            with open(omit, "w") as fh:
                fh.write("\n".join(lines) + "\n")
            self.assertEqual(ppa.map_rtlil(il, d["top"], lib, mp), ppa.map_rtlil(il, d["top"], lib, ppa.MappedPins(pins, script=omit)))

    def test_the_mapped_columns_are_bit_exact_across_processes_hash_seeds_and_temp_dirs(self):
        """The CLI in separate processes under three hash seeds and two TMPDIRs, serially and two at a time: byte-identical
        output (sorted JSON), mapped block included."""
        cmd = [sys.executable, os.path.join(HERE, "ppa.py"), os.path.join(SVGOLF, "tasks", "add", "reference", "add_n.sv"),
               "--task", os.path.join(SVGOLF, "tasks", "add")]
        outs = []
        with tempfile.TemporaryDirectory() as t1, tempfile.TemporaryDirectory() as t2:
            procs = []
            for seed, tmpd in (("0", t1), ("5", t2), ("123", t1)):
                env = dict(os.environ, PYTHONHASHSEED=seed, PYTHONDONTWRITEBYTECODE="1", TMPDIR=tmpd)
                procs.append(subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env))
            for p in procs:
                out, err = p.communicate()
                self.assertEqual(p.returncode, 0, out + err)
                outs.append(out)
        self.assertEqual(outs[0], outs[1])
        self.assertEqual(outs[0], outs[2])
        res = json.loads(outs[0])
        m = res["ppa"]["mapped"]
        self.assertEqual((m["area_um2_sky130_mapped_v1"], m["mapped_delay_sky130_v1"], m["mapped_cells_sky130_v1"]), (440.4224, 6279, 48))

    def test_no_mapped_flag_skips_the_mapping_and_the_default_has_it(self):
        cmd = [sys.executable, os.path.join(HERE, "ppa.py"), os.path.join(SVGOLF, "tasks", "add", "reference", "add_n.sv"),
               "--task", os.path.join(SVGOLF, "tasks", "add")]
        r = subprocess.run(cmd + ["--no-mapped"], capture_output=True, text=True,
                           env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertNotIn("mapped", json.loads(r.stdout)["ppa"])
        r = subprocess.run(cmd[:2] + ["--netlist-in", os.devnull, "--mapped-netlist", "x.v"], capture_output=True, text=True)
        self.assertEqual(r.returncode, 2)

    def test_unscorable_design_is_loud(self):
        """A flip-flop is refused by the pinned flow itself (its netlist has a cell the GE table does not price)."""
        import score
        with self.assertRaises(score.ScoreError):
            ppa.score_and_weigh([os.path.join(HERE, "tests", "reg.sv")], "reg1", {})


@needs_lib
class ClockedTest(unittest.TestCase):
    """The clocked flow (score.py --seq): dfxtp_1 area, the register-to-register period from the liberty's clock-to-Q
    and setup, the unit depth equal to the flow's `ltp -noff`."""

    @classmethod
    def setUpClass(cls):
        cls.lib, cls.pins = ppa.open_library()
        cls.ft = ppa.FlopTiming(cls.lib, cls.pins)

    def test_one_flop_is_clock_to_q(self):
        """d -> D (setup 112 ps) and Q -> y (clock-to-Q 349 ps into the 10 fF output load): T is the clock-to-Q."""
        text = netlist(gate("DFF_P", "_1_", C="c", D="a", Q="y"), ports="input a;\n  input c;\n  output y;")
        a = ppa.analyze(text, self.lib, self.pins)
        load = self.pins.po_load_pf
        cq = max(self.ft.cq[k].at(self.pins.pi_slew_ns, load) for k in ("cell_rise", "cell_fall"))
        self.assertAlmostEqual(a.t_ns, cq)
        self.assertEqual((a.flops, a.cells, a.area_e4, a.unit_depth), (1, 1, self.ft.area_e4, 0))

    @unittest.skipUnless(have_flow(), "the pinned flow is not available")
    def test_counter(self):
        sv = os.path.join(SVGOLF, "tests", "seq_counter", "reference", "cnt.sv")
        r = ppa.score_and_weigh([sv], "cnt", {"N": 8}, mapped=False, flow="seq")      # checks depth and gate count too
        p = r["ppa"]
        self.assertEqual((p["sequential"], p["flops"], p["cell_hist_sky130"]["dfxtp_1"]), (True, 8, 8))
        self.assertTrue(p["critical"]["output"].startswith("D:"))            # a register-to-register path
        self.assertGreater(p["delay_ps_sky130"], 349 + 112)                   # clock-to-Q + logic + setup
        self.assertEqual(r, ppa.score_and_weigh([sv], "cnt", {"N": 8}, mapped=False, flow="seq"))

    def test_malformed_flop_refused(self):
        with self.assertRaises(ppa.PpaError):
            ppa.analyze(netlist(gate("DFF_P", "_1_", D="a", Q="y")), self.lib, self.pins)


class SummaryLineTest(unittest.TestCase):
    """The one stderr line after the JSON (`summary_line`, decided 2026-11-12): the weighed area and delay, a clocked
    netlist's period, with --latency L the ranked score area x L cycles x period (leaderboard/combined.py's product),
    and a comb design's area x delay; the JSON itself is unchanged (stdout stays one JSON document)."""

    def test_the_line(self):
        comb = {"ppa": {"area_um2_sky130": 460.4416, "area_e4um2_sky130": 4604416, "delay_ps_sky130": 2611}}
        self.assertEqual(ppa.summary_line(comb),
                         "ppa (sky130 A0'): area 460.4416 um^2, delay 2611 ps; area x delay = 1202.21 um2*ns")
        a7 = {"ppa": {"area_um2_asap7": 6.9984, "area_e5um2_asap7": 699840, "delay_ps_asap7": 563}}
        self.assertEqual(ppa.summary_line(a7, "asap7"),
                         "ppa (asap7 A0'): area 6.9984 um^2, delay 563 ps; area x delay = 3.94 um2*ns")
        seq = {"ppa": {"area_um2_sky130": 87173.6064, "area_e4um2_sky130": 871736064, "delay_ps_sky130": 10696,
                       "sequential": True}}
        self.assertEqual(ppa.summary_line(seq), "ppa (sky130 A0'): area 87173.6064 um^2, period 10696 ps")
        self.assertEqual(ppa.summary_line(seq, latency=4),
                         "ppa (sky130 A0'): area 87173.6064 um^2, period 10696 ps; score: 87173.6064 um^2 x 4 cycles "
                         "x 10696 ps = 3729635.58 um2*ns")
        self.assertIn("x 1 cycle x 10696 ps = 932408.89 um2*ns", ppa.summary_line(seq, latency=1))
        self.assertIsNone(ppa.summary_line({"ppa": {"available": False, "reason": "no liberty"}}))
        self.assertIsNone(ppa.summary_line({"error": "x"}))

    def test_latency_needs_a_clocked_run(self):
        sv = os.path.join(SVGOLF, "tasks", "add", "reference", "add_n.sv")
        for more in (["--latency", "2"], ["--seq", "--latency", "0"]):
            r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), sv, "--task",
                                os.path.join(SVGOLF, "tasks", "add")] + more,
                               capture_output=True, text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
            self.assertEqual(r.returncode, 2, r.stderr)
            self.assertIn("--latency L takes --seq", r.stderr)

    @needs_flow
    def test_the_cli_prints_the_json_then_the_line(self):
        sv = os.path.join(SVGOLF, "tests", "seq_counter", "reference", "cnt.sv")
        r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), sv, "--top", "cnt", "--param", "N=8", "--seq",
                            "--latency", "1"], capture_output=True, text=True,
                           env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        self.assertEqual(r.returncode, 0, r.stderr)
        res = json.loads(r.stdout)                       # stdout is the JSON alone
        p = res["ppa"]
        self.assertEqual(r.stderr.splitlines()[-1], ppa.summary_line(res, latency=1))
        self.assertIn(f"period {p['delay_ps_sky130']} ps; score: {p['area_um2_sky130']} um^2 x 1 cycle x "
                      f"{p['delay_ps_sky130']} ps = ", r.stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
