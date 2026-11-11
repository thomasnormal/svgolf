#!/usr/bin/env python3.12
"""Tests for ppa.py's ASAP7 library (`--pdk asap7`, score/ppa_pins_asap7.json): what the port added to the sky130 flows, on
a synthetic two-file liberty in ps and fF (always runs: unit conversion, unquoted cell names and a missing semicolon, 5-decimal
areas, per-file hashes, a Yosys gate built from two cells, the QN-only flop with its Q inverter and its transposed setup table,
a read below a table's grid read at the floor, separate TIELO/TIEHI cells within a pinned max_capacitance), and, when the
pinned asap7 files are present ($SVGOLF_ASAP7_LIB or score/lib/asap7/), the real library: the pinned identity, every gate
build against the Yosys gate semantics and as the least-area build, the flop, the A1' script's dont_use list against the cell
policy, the measured low-edge claim behind timing.below_grid, the golden columns of six designs through the pinned flow (three
combinational with A1', three clocked) and bit-identical records across processes and hash seeds. sky130 stays the default:
its pins and reading are checked unchanged where it matters here (score/test_ppa.py covers the rest).

    python3.12 score/test_ppa_asap7.py

Without the asap7 files the real-library tests are SKIPPED; SVGOLF_PPA_REQUIRE_ASAP7=1 turns that into a failure (its own
variable: tests/run.py sets SVGOLF_PPA_REQUIRE_LIB=1 wherever the sky130 liberty is present).
"""
import fnmatch
import itertools
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import ppa  # noqa: E402

A7_PINS_PATH = ppa.pdk_paths("asap7")[0]
A7 = ppa.Pins(A7_PINS_PATH)
SFX = A7.suffix
REAL_DIR = ppa.find_liberty(None, A7)
HAVE_LIB = os.path.isdir(REAL_DIR) and all(os.path.isfile(os.path.join(REAL_DIR, f["file"])) for f in A7.lib_files)
REQUIRE_LIB = os.environ.get("SVGOLF_PPA_REQUIRE_ASAP7") == "1"
needs_lib = unittest.skipUnless(HAVE_LIB, f"the pinned asap7 liberty files are absent ({REAL_DIR}); run "
                                          "`python3.12 score/ppa.py --pdk asap7 --fetch-liberty`")


def have_flow():
    import score
    if shutil.which(score.yosys_bin()) is None:
        return False
    try:
        import pyslang  # noqa: F401
    except ImportError:
        return False
    return True


needs_flow = unittest.skipUnless(HAVE_LIB and have_flow(), "needs the pinned asap7 files, Yosys and pyslang")


# ------------------------------------------------------------------------------------------------ a synthetic asap7-like library
def _tbl(kind, tpl, a, b, c, i1=(5.0, 50.0), i2=(1.0, 20.0)):
    """A 2x2 table of f(x1, x2) = a + b*x1 + c*x2 in ps on x1 in i1 (ps), x2 in i2 (fF): bilinear reads reproduce f."""
    f = lambda x, y: repr(a + b * x + c * y)
    return (f'        {kind} ({tpl}) {{\n          index_1 ("{i1[0]}, {i1[1]}");\n          index_2 ("{i2[0]}, {i2[1]}");\n'
            f'          values ( "{f(i1[0], i2[0])}, {f(i1[0], i2[1])}", "{f(i1[1], i2[0])}, {f(i1[1], i2[1])}" );\n        }}\n')


def _arc(rel, sense="negative_unate", d=(5.0, 0.3, 3.0), t=(4.0, 0.2, 6.0)):
    return (f'      timing () {{\n        related_pin : "{rel}";\n        timing_sense : {sense};\n        timing_type : combinational;\n'
            + _tbl("cell_rise", "dly", *d) + _tbl("cell_fall", "dly", *d)
            + _tbl("rise_transition", "dly", *t) + _tbl("fall_transition", "dly", *t) + "      }\n")


def _header(name, dmt=320):
    return (f"library ({name}) {{\n  /* BSD 3-Clause (synthetic) */\n  time_unit : \"1ps\";\n  voltage_unit : \"1V\";\n"
            f"  capacitive_load_unit (1, ff);\n  default_max_transition : {dmt};\n"
            "  lu_table_template (dly) {\n    variable_1 : input_net_transition;\n    variable_2 : total_output_net_capacitance;\n"
            '    index_1 ("1, 2");\n    index_2 ("1, 2");\n  }\n'
            "  lu_table_template (cons) {\n    variable_1 : constrained_pin_transition;\n    variable_2 : related_pin_transition;\n"
            '    index_1 ("1, 2");\n    index_2 ("1, 2");\n  }\n')


def _cell(name, area, inputs, out, fn, arcs, max_cap=20.0, semi=True):
    pins = "".join(f"    pin ({p}) {{\n      direction : input;\n      capacitance : 0.6;\n      rise_capacitance : 0.62;\n"
                   f"      fall_capacitance : 0.58;\n      max_transition : 320;\n    }}\n" for p in inputs)
    return (f"  cell ({name}{SFX}) {{\n    area : {area}{';' if semi else ''}\n" + pins
            + f"    pin ({out}) {{\n      direction : output;\n      function : \"{fn}\";\n"
            + (f"      max_capacitance : {max_cap};\n" if max_cap else "") + arcs + "    }\n  }\n")


def comb_lib(inv_fn="!A"):
    """File 1: INVx1 (area with no semicolon, as asap7's INVBUF files), NAND2xp5, NOR2xp33, AO22x1, BUFx2, TIEHIx1, TIELOx1."""
    t = [_header("synth_comb")]
    t.append(_cell("INVx1", "0.04374", ["A"], "Y", inv_fn, _arc("A"), semi=False))
    t.append(_cell("NAND2xp5", "0.05832", ["A", "B"], "Y", "!(A * B)", _arc("A") + _arc("B", d=(6.0, 0.3, 3.0))))
    t.append(_cell("NOR2xp33", "0.05832", ["A", "B"], "Y", "!(A + B)", _arc("A") + _arc("B")))
    t.append(_cell("AO22x1", "0.13122", ["A1", "A2", "B1", "B2"], "Y", "(A1 * A2) + (B1 * B2)",
                   "".join(_arc(p, "positive_unate", d=(9.0, 0.2, 2.0)) for p in ("A1", "A2", "B1", "B2"))))
    t.append(_cell("BUFx2", "0.0729", ["A"], "Y", "A", _arc("A", "positive_unate", d=(8.0, 0.1, 1.0), t=(3.0, 0.1, 2.0)),
                   max_cap=40.0))
    t.append(f"  cell (TIEHIx1{SFX}) {{\n    area : 0.04374;\n    pin (H) {{\n      direction : output;\n      function : \"1\";\n    }}\n  }}\n")
    t.append(f"  cell (TIELOx1{SFX}) {{\n    area : 0.04374;\n    pin (L) {{\n      direction : output;\n      function : \"0\";\n    }}\n  }}\n")
    return "".join(t) + "}\n"


def seq_lib(next_state="!D"):
    """File 2: DFFHQNx1, QN only (ff IQN = !D at CLK's rise), CLK->QN rising_edge, setup_rising stored constrained-first."""
    cq = "".join(_tbl(k, "dly", 30.0, 0.1, 2.0) for k in ("cell_rise", "cell_fall", "rise_transition", "fall_transition"))
    # setup = 10 + 0.5 * D transition - 0.1 * CLK transition, stored with index_1 = D (constrained), index_2 = CLK (related)
    su = "".join(_tbl(k, "cons", 10.0, 0.5, -0.1, i1=(5.0, 50.0), i2=(5.0, 50.0)) for k in ("rise_constraint", "fall_constraint"))
    return (_header("synth_seq") + f"  cell (DFFHQNx1{SFX}) {{\n    area : 0.2916;\n"
            "    pin (QN) {\n      direction : output;\n      function : \"IQN\";\n      max_capacitance : 46.08;\n"
            "      timing () {\n        related_pin : \"CLK\";\n        timing_sense : non_unate;\n        timing_type : rising_edge;\n"
            + cq + "      }\n    }\n"
            "    pin (CLK) {\n      clock : true;\n      direction : input;\n      capacitance : 0.47;\n      max_transition : 320;\n    }\n"
            "    pin (D) {\n      direction : input;\n      capacitance : 0.56;\n      max_transition : 320;\n"
            "      timing () {\n        related_pin : \"CLK\";\n        timing_type : setup_rising;\n" + su + "      }\n    }\n"
            f"    ff (IQN,IQNN) {{\n      clocked_on : \"CLK\";\n      next_state : \"{next_state}\";\n    }}\n  }}\n}}\n")


def write_pins(path, files, **over):
    """The real asap7 pins with the liberty files replaced by `files` (paths), the repair's buffers and the input drive set to
    the synthetic BUFx2, and top-level overrides."""
    with open(A7_PINS_PATH) as fh:
        raw = json.load(fh)
    raw["liberty"]["files"] = [{"file": os.path.basename(p), "sha256": ppa.sha256_file(p), "bytes": os.path.getsize(p)}
                               for p in files]
    raw["repair"]["buffers"] = ["BUFx2"]
    raw["timing"]["input_drive"]["default"] = "BUFx2" + SFX
    raw["timing"]["input_drive"]["allowed"] = ["BUFx2" + SFX]
    for k, v in over.items():
        raw[k] = v
    with open(path, "w") as fh:
        json.dump(raw, fh)
    return ppa.Pins(path)


def netlist(body, ports, wires=""):
    names = ", ".join(re.findall(r"(?:input|output)\s*(?:\[[^\]]*\])?\s*(\w+)", ports))
    return f"module tiny({names});\n  {wires}\n  {ports}\n{body}endmodule\n"


def gate(kind, inst, **pins):
    return f"  \\$_{kind}_  {inst} (" + ", ".join(f".{k}({v})" for k, v in pins.items()) + ");\n"


class SyntheticTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.mkdtemp(prefix="ppa-asap7-test-")
        cls.libdir = os.path.join(cls.dir, "lib")
        os.makedirs(cls.libdir)
        cls.files = [os.path.join(cls.libdir, "comb.lib"), os.path.join(cls.libdir, "seq.lib")]
        for p, text in zip(cls.files, (comb_lib(), seq_lib())):
            with open(p, "w") as fh:
                fh.write(text)
        cls.pins = write_pins(os.path.join(cls.dir, "pins.json"), cls.files)
        cls.lib = ppa.Liberty(cls.libdir, cls.pins)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir, ignore_errors=True)

    def test_units_syntax_and_areas(self):
        """ps and fF read as ns and pF (one division by 1000); an unquoted cell name and an area line without its semicolon are
        read; areas are integers in 1e-5 um^2; the library's identity is the set hash of its files."""
        inv = self.lib.cell("INVx1" + SFX)
        self.assertEqual(inv.area_e4, 4374)
        self.assertEqual(inv.pin_cap_e["A"], {"r": 0.62 / 1000, "f": 0.58 / 1000})
        self.assertEqual(inv.max_cap["Y"], 20.0 / 1000)
        self.assertEqual(inv.max_trans, {"A": 320 / 1000})
        t = inv.arcs["Y"][0].tbl["cell_rise"]
        self.assertEqual((t.i1, t.i2), ([5.0 / 1000, 50.0 / 1000], [1.0 / 1000, 20.0 / 1000]))
        self.assertAlmostEqual(t.at(0.020, 0.010), (5.0 + 0.3 * 20 + 3.0 * 10) / 1000, places=15)
        self.assertEqual(self.lib.default_max_transition, 0.32)
        self.assertEqual(self.lib.sha256, ppa.set_sha256(self.pins.lib_files))
        self.assertEqual(len(self.lib.cell_names), 8)

    def test_library_defects_are_loud(self):
        bad = os.path.join(self.dir, "badlib")
        os.makedirs(bad, exist_ok=True)
        # a file whose bytes are not the pinned ones
        for p in self.files:
            shutil.copyfile(p, os.path.join(bad, os.path.basename(p)))
        with open(os.path.join(bad, "seq.lib"), "a") as fh:
            fh.write("\n")
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.Liberty(bad, self.pins)
        self.assertIn("is not the pinned", str(cm.exception))
        # a cell in two files; a file in other units
        dupdir = os.path.join(self.dir, "dupdir")
        os.makedirs(dupdir, exist_ok=True)
        shutil.copyfile(self.files[0], os.path.join(dupdir, "comb.lib"))
        dup = os.path.join(dupdir, "dup.lib")
        with open(dup, "w") as fh:
            fh.write(comb_lib())
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.Liberty(dupdir, write_pins(os.path.join(self.dir, "dup.json"), [os.path.join(dupdir, "comb.lib"), dup]))
        self.assertIn("duplicate cell", str(cm.exception))
        ns = os.path.join(self.dir, "ns.lib")
        with open(ns, "w") as fh:
            fh.write(comb_lib().replace('time_unit : "1ps"', 'time_unit : "1ns"'))
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.Liberty(self.dir, write_pins(os.path.join(self.dir, "ns.json"), [ns]))
        self.assertIn("differ from the pinned", str(cm.exception))
        # a directory that does not exist
        with self.assertRaises(ppa.PpaError):
            ppa.Liberty(os.path.join(self.dir, "nowhere"), self.pins)

    def test_a_gate_built_from_two_cells(self):
        """MUX = INVx1 on S + AO22x1: two cells, weighed and timed as cells, one gate of the unit depth and of the scored count;
        the helper has a fresh name; the S path is INV then AO22, the data paths AO22 alone."""
        text = netlist(gate("MUX", "_1_", A="a", B="b", S="s", Y="y"), "input a;\n  input b;\n  input s;\n  output y;")
        a = ppa.analyze(text, self.lib, self.pins)
        self.assertEqual(a.hist, {"AO22x1": 1, "INVx1": 1})
        self.assertEqual((a.cells, a.unit_depth, a.scored_gates), (2, 1, 1))
        self.assertEqual(a.area_e4, 4374 + 13122)
        self.assertEqual([n for n, _, _ in a.path][:2], ["s", "svgm0_n"])
        self.assertIn("INVx1_ASAP7_75t_R svgm0 (.A(s), .Y(svgm0_n));", a.repair["text"])
        for g in ("ANDNOT", "ORNOT"):
            b = ppa.analyze(netlist(gate(g, "_1_", A="a", B="b", Y="y"), "input a;\n  input b;\n  output y;"), self.lib,
                            self.pins)
            self.assertEqual((b.cells, b.unit_depth, b.scored_gates), (2, 1, 1), g)

    def test_a_wrong_build_is_refused(self):
        with open(A7_PINS_PATH) as fh:
            gates = json.load(fh)["gates"]
        gates["MUX"]["cells"][1]["conn"] = {"A1": "B", "A2": "sn", "B1": "A", "B2": "S"}     # S ? A : B
        pins = write_pins(os.path.join(self.dir, "wrong.json"), self.files, gates=gates)
        text = netlist(gate("MUX", "_1_", A="a", B="b", S="s", Y="y"), "input a;\n  input b;\n  input s;\n  output y;")
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze(text, ppa.Liberty(self.libdir, pins), pins)
        self.assertIn("does not compute", str(cm.exception))
        gates["MUX"]["cells"][1]["conn"] = {"A1": "A", "A2": "nope", "B1": "B", "B2": "S"}
        with self.assertRaises(ppa.PpaError):
            write_pins(os.path.join(self.dir, "wrong2.json"), self.files, gates=gates)

    def test_below_the_grid_is_read_at_the_floor(self):
        """INVx1 driving one NAND2 pin (0.62 fF, below the 1 fF grid): read at 1 fF, counted, legal. The same read under
        timing.below_grid = reject is a violation the repair cannot fix."""
        text = netlist(gate("NOT", "_1_", A="a", Y="_0_") + gate("NAND", "_2_", A="_0_", B="b", Y="y"),
                       "input a;\n  input b;\n  output y;", "wire _0_;")
        a = ppa.analyze(text, self.lib, self.pins)
        self.assertGreater(a.audit.floored, 0)
        self.assertEqual(a.audit.violations(), 0)
        inv = self.lib.cell("INVx1" + SFX)
        t0 = a.design.arr[("_0_", "f")][0] - a.design.arr[("a", "r")][0]
        self.assertAlmostEqual(t0, inv.arcs["Y"][0].tbl["cell_fall"].at(a.design.arr[("a", "r")][1], 0.001), places=12)
        with open(A7_PINS_PATH) as fh:
            timing = json.load(fh)["timing"]
        timing["below_grid"] = "reject"
        timing["input_drive"] = {"default": "BUFx2" + SFX, "allowed": ["BUFx2" + SFX], "shape": "BUFx2"}
        strict = write_pins(os.path.join(self.dir, "strict.json"), self.files, timing=timing)
        with self.assertRaises(ppa.IllegalNetlist) as cm:
            ppa.analyze(text, ppa.Liberty(self.libdir, strict), strict)
        self.assertIn("BELOW", str(cm.exception))

    def test_above_the_grid_is_still_repaired(self):
        """A NAND2 output driving 40 output bits (100 fF, over its 20 fF max_capacitance): buffered, as on sky130."""
        body = gate("NAND", "_1_", A="a", B="b", Y="_0_") + "".join(f"  assign y[{k}] = _0_;\n" for k in range(40))
        a = ppa.analyze(netlist(body, "input a;\n  input b;\n  output [39:0] y;", "wire _0_;"), self.lib, self.pins)
        self.assertGreater(a.repair["buffers"], 1)
        self.assertEqual(a.audit.violations(), 0)

    def test_tie_cells_one_per_constant_within_the_pinned_limit(self):
        """30 constant-1 output bits (75 fF) need two TIEHIx1 within the pinned 46.08 fF (the cell declares none); one
        constant-0 bit one TIELOx1; the written netlist has both kinds and reads back."""
        body = "".join(f"  assign y[{k}] = 1'h1;\n" for k in range(30)) + "  assign z = 1'h0;\n" + gate("NOT", "_1_", A="a", Y="w")
        a = ppa.analyze(netlist(body, "input a;\n  output [29:0] y;\n  output z;\n  output w;"), self.lib, self.pins)
        self.assertEqual((a.ties, a.hist["TIEHIx1"], a.hist["TIELOx1"]), (3, 2, 1))
        self.assertIn("/* constants: 2 TIEHIx1 + 1 TIELOx1 tie cells */", a.repair["text"])
        self.assertEqual(a.audit.violations(), 0)
        # without a repair: one cell per constant used, the TIEHIx1 over the pinned limit (rejected, as sky130's conb_1 would be)
        with self.assertRaises(ppa.IllegalNetlist) as cm:
            ppa.analyze(netlist(body, "input a;\n  output [29:0] y;\n  output z;\n  output w;"), self.lib, self.pins,
                        repair_netlist=False)
        self.assertEqual(cm.exception.summary["over_max_capacitance"], 1)
        self.assertIn("tie cell TIEHIx1 H driving constant 1", str(cm.exception))

    def test_the_qn_flop_and_its_q_inverter(self):
        """A $_DFF_P_ is DFFHQNx1 + INVx1: area of both, the inverter a real cell driving the scored Q net, not a gate of the
        unit depth; clock-to-Q is CLK->QN at the inverter's input then the inverter; setup is read from a table stored the
        other way round (index_1 the D transition)."""
        text = netlist("  \\$_DFF_P_  _r_ (.C(clk), .D(_0_), .Q(q));\n" + gate("NOT", "_1_", A="q", Y="_0_")
                       + "  assign y = q;\n", "input clk;\n  output y;", "wire _0_;\n  wire q;")
        a = ppa.analyze(text, self.lib, self.pins)
        self.assertEqual(a.hist, {"DFFHQNx1": 1, "INVx1": 2})
        self.assertEqual((a.flops, a.unit_depth, a.scored_gates), (1, 1, 2))
        self.assertEqual(a.area_e4, 29160 + 2 * 4374)
        self.assertIn("DFFHQNx1_ASAP7_75t_R _r_ (.CLK(clk), .D(_0_), .QN(svgq0_n));", a.repair["text"])
        ft = ppa.FlopTiming(self.lib, self.pins)
        self.assertAlmostEqual(ft.setup["rise_constraint"].at(0.020, 0.030), (10.0 + 0.5 * 30 - 0.1 * 20) / 1000, places=15)
        # the QN flop without a Q inverter in the pins, or a Q flop with one: refused
        with open(A7_PINS_PATH) as fh:
            flop = json.load(fh)["flop"]
        bare = dict(flop, q_inverter=None)
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze(text, self.lib, write_pins(os.path.join(self.dir, "bare.json"), self.files, flop=bare))
        self.assertIn("form no Q", str(cm.exception))
        qlib = os.path.join(self.dir, "qlib")
        os.makedirs(qlib, exist_ok=True)
        shutil.copyfile(self.files[0], os.path.join(qlib, "comb.lib"))
        with open(os.path.join(qlib, "seq.lib"), "w") as fh:
            fh.write(seq_lib(next_state="D"))
        qp = write_pins(os.path.join(self.dir, "q.json"), [os.path.join(qlib, "comb.lib"), os.path.join(qlib, "seq.lib")])
        with self.assertRaises(ppa.PpaError) as cm:
            ppa.analyze(text, ppa.Liberty(qlib, qp), qp)
        self.assertIn("invert it", str(cm.exception))

    def test_columns_carry_the_library(self):
        text = netlist(gate("NAND", "_1_", A="a", B="b", Y="y"), "input a;\n  input b;\n  output y;")
        a = ppa.analyze(text, self.lib, self.pins)
        c = ppa.columns(a, self.pins, self.lib, "x")
        self.assertEqual((c["area_um2_asap7"], c["area_e5um2_asap7"], c["cells_asap7"], c["pdk"]), (0.05832, 5832, 1, "asap7"))
        self.assertFalse(any("sky130" in k for k in c))
        self.assertEqual(c["setup"]["po_load_ff"], 2.5)
        self.assertEqual(set(c["liberty_files"]), {"comb.lib", "seq.lib"})


class Sky130DefaultTest(unittest.TestCase):
    def test_sky130_is_the_default_and_its_pins_are_unchanged(self):
        p = ppa.Pins()
        self.assertEqual((p.pdk, p.col, p.area_decimals, p.multi, p.suffix, p.below_grid), ("sky130", "sky130", 4, False, "", "reject"))
        self.assertIs(p.policy, ppa.POLICY)
        self.assertEqual(p.flop, {"cell": "dfxtp_1", "clock": "CLK", "d": "D", "q": "Q", "q_inverter": None})
        self.assertEqual(p.tie_cells, {"0": "conb_1", "1": "conb_1"})
        self.assertEqual((p.pi_slew_ns, p.po_load_pf), (0.05, 0.010))

    def test_sky130_reading_needs_no_semicolon_tolerance(self):
        path = ppa.find_liberty(None, ppa.Pins())
        if not os.path.isfile(path):
            self.skipTest("the sky130 liberty is absent")
        with open(path) as fh:
            text = re.sub(r"\\\s*\n", " ", re.sub(r"/\*.*?\*/", "", fh.read(), flags=re.S))
        self.assertEqual(ppa._NOSEMI_RE.findall(text), [])


# ------------------------------------------------------------------------------------------------ the real library
class RealLibraryRequired(unittest.TestCase):
    def test_liberty_present_when_required(self):
        if REQUIRE_LIB and not HAVE_LIB:
            self.fail(f"SVGOLF_PPA_REQUIRE_ASAP7=1 but the pinned asap7 files are absent: {REAL_DIR}")


@needs_lib
class RealLibraryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pins = A7
        cls.lib = ppa.Liberty(REAL_DIR, A7)

    def test_pinned_identity(self):
        self.assertEqual(self.lib.sha256, "5ece07acb7ece6a9fad109eadccbf88cce141dd8aa02f877205ee706cc99057a")
        self.assertEqual(len(self.lib.cell_names), 202)
        self.assertEqual([round(x * 1000) for x in self.lib.dmts], [320, 4000, 320, 320, 320])
        self.assertEqual(self.lib.default_max_transition, 0.32)
        self.assertEqual((self.pins.pi_slew_ns, self.pins.po_load_pf), (0.02, 0.0025))
        with open(ppa.pdk_paths("asap7")[1]) as fh:
            self.assertEqual(json.load(fh)["liberty_sha256"], self.lib.sha256)

    def test_every_gate_build_computes_its_gate_at_the_documented_price(self):
        self.assertEqual(sorted(self.pins.gates), sorted(ppa.GATE_SEMANTICS))
        nand2 = self.lib.cell(self.pins.full("NAND2xp5")).area_e4
        price = {}
        for g in self.pins.gates:
            ppa.check_gate_cell(self.lib, self.pins, g)
            price[g] = sum(self.lib.cell(self.pins.full(c)).area_e4 for c, _, _, _ in self.pins.gate_cells[g]) / nand2
        self.assertEqual(price, {"NOT": 0.75, "NAND": 1.0, "NOR": 1.0, "AND": 1.5, "OR": 1.5, "XOR": 2.25, "XNOR": 2.25,
                                 "MUX": 3.0, "ANDNOT": 1.75, "ORNOT": 1.75})

    def test_every_gate_build_is_a_least_area_build(self):
        """No build of one or two single-output logic cells (distinct signals on a cell's inputs) is smaller than the pinned
        one: an exhaustive search over the cells no larger than the pinned build."""
        cells = [self.lib.cell(n) for n in self.lib.cell_names if ppa.pins_class(n, self.pins) == "logic"
                 and self.lib.file_of[n] < 4]
        cells = [c for c in cells if len(c.outputs) == 1 and 0 < len(c.inputs) <= 4]
        for gate, (ins, sem) in ppa.GATE_SEMANTICS.items():
            pinned = sum(self.lib.cell(self.pins.full(c)).area_e4 for c, _, _, _ in self.pins.gate_cells[gate])
            n, mask = len(ins), (1 << (1 << len(ins))) - 1
            vec = {p: sum(1 << r for r in range(1 << n) if (r >> i) & 1) for i, p in enumerate(ins)}
            want = sem([vec[p] for p in ins], mask)
            small = [c for c in cells if c.area_e4 < pinned]
            for c in small:
                for perm in itertools.permutations(ins, len(c.inputs)):
                    env = dict(zip(c.inputs, (vec[p] for p in perm)))
                    self.assertNotEqual(ppa.eval_function(c.function[c.outputs[0]], env, mask), want, (gate, c.name))
            for c1 in small:
                for p1 in itertools.permutations(ins, min(len(c1.inputs), n)) if len(c1.inputs) <= n else ():
                    v1 = ppa.eval_function(c1.function[c1.outputs[0]], dict(zip(c1.inputs, (vec[p] for p in p1))), mask)
                    sig = dict(vec, n=v1)
                    for c2 in small:
                        if c1.area_e4 + c2.area_e4 >= pinned or len(c2.inputs) > n + 1:
                            continue
                        for p2 in itertools.permutations(list(ins) + ["n"], len(c2.inputs)):
                            if "n" in p2:
                                env = dict(zip(c2.inputs, (sig[p] for p in p2)))
                                self.assertNotEqual(ppa.eval_function(c2.function[c2.outputs[0]], env, mask), want,
                                                    (gate, c1.name, c2.name))

    def test_the_flop(self):
        ft = ppa.FlopTiming(self.lib, self.pins)
        self.assertEqual((ft.name, ft.area_e4, ft.q_pin), (self.pins.full("DFFHQNx1"), 29160, "QN"))
        g = self.lib.group(ft.name)
        raw = [t for p in g.find("pin") if p.args[0] == "D" for t in p.find("timing") if t.attrs.get("timing_type") ==
               "setup_rising"][0].find("rise_constraint")[0]
        v = [[float(x) for x in r.split(",")] for r in raw.attrs["values"]]
        # stored [D transition][CLK transition]; read (CLK transition, D transition)
        self.assertEqual(ft.setup["rise_constraint"].v[2][5], v[5][2] / 1000)
        self.assertEqual(ft.setup["rise_constraint"].i1, [x / 1000 for x in (5, 10, 20, 40, 80, 160, 320)])

    def test_the_mapped_script_excludes_exactly_the_non_logic_cells(self):
        with open(ppa.pdk_paths("asap7")[2]) as fh:
            script = fh.read()
        globs = re.findall(r"-dont_use (\S+)", script)
        mp = ppa.MappedPins(self.pins)
        comb = [n for n in self.lib.cell_names if os.path.basename(self.lib.paths[self.lib.file_of[n]]) in mp.abc_files]
        self.assertEqual(len(comb), 169)
        excluded = sorted(n for n in comb if any(fnmatch.fnmatchcase(n, g) for g in globs))
        self.assertEqual(excluded, sorted(n for n in comb if ppa.pins_class(n, self.pins) != "logic"))
        self.assertEqual(mp.abc_files[0], "asap7sc7p5t_SIMPLE_RVT_TT_nldm_211120.lib")     # INVBUF first crashes ABC 1.01

    def test_the_low_edge_claim_of_below_grid(self):
        """timing.below_grid's measurement: every delay table rises from its first point along both axes; transition tables
        rise along the load and drop at most 0.39 ps along the input transition; the flop's setup rises along D's transition
        at the 20 ps clock row."""
        worst = 0.0
        for n in self.lib.cell_names:
            if ppa.pins_class(n, self.pins) not in ("logic", "tie"):
                continue
            for arcs in self.lib.cell(n).arcs.values():
                for a in arcs:
                    for k, t in a.tbl.items():
                        for i in range(len(t.i1)):
                            self.assertGreaterEqual(t.v[i][1], t.v[i][0], (n, k))
                        for j in range(len(t.i2)):
                            if k.startswith("cell_"):
                                self.assertGreaterEqual(t.v[1][j], t.v[0][j], (n, k))
                            else:
                                worst = max(worst, t.v[0][j] - t.v[1][j])
        self.assertLess(worst, 0.00040)
        ft = ppa.FlopTiming(self.lib, self.pins)
        for k, t in ft.setup.items():
            row = t.i1.index(self.pins.pi_slew_ns)
            self.assertGreaterEqual(t.v[row][1], t.v[row][0], k)


# the six designs through the pinned flow: (task, source, clocked, area_e5um2_asap7, delay_ps_asap7, cells_asap7, unit_depth,
# repair buffers, repaired netlist sha256 prefix, A1' (area_e5um2_asap7_mapped_v1, mapped_delay_asap7_v1, mapped cells))
GOLDEN = [
    ("add", "tasks/add/reference/add_n.sv", False, 699840, 563, 80, 33, 0, "3f31f3f295487ce1", (710046, 328, 69)),
    ("mul", "tasks/mul/reference/mul_n.sv", False, 12393000, 1981, 1411, 88, 0, "dc39f8141d84f2ff", (11091006, 1784, 1112)),
    ("aes_sbox", "tasks/aes_sbox/reference/sbox_bp.sv", False, 1335528, 704, 141, 21, 0, "19f2288bdc50054a", (1221804, 653, 119)),
    ("arbiter", "tasks/arbiter/reference/rr_mask.sv", True, 1215972, 464, 138, 17, 0, "35b5e4557491b5cd", None),
    ("matmul", "tasks/matmul/reference/matmul_g1.sv", True, 133472610, 1539, 14383, 61, 6, "c727a8839baa1704", None),
    ("sorter", "tasks/sorter/reference/sorter_ins.sv", True, 8568666, 512, 998, 15, 0, "616d75ed0732cc6d", None),
]


@needs_flow
class GoldenTest(unittest.TestCase):
    def test_golden_columns(self):
        import score
        lib = ppa.Liberty(REAL_DIR, A7)
        for task, src, seq, area, delay, cells, depth, bufs, sha, mapped in GOLDEN:
            with self.subTest(task=task):
                t = score.load_task(os.path.join(SVGOLF, "tasks", task))
                top, params = score.task_scoring_point(t)
                r = ppa.score_and_weigh([os.path.join(SVGOLF, src)], top, params, REAL_DIR, A7, mapped=not seq,
                                        flow="seq" if seq else "comb")
                b = r["ppa"]
                self.assertEqual((b["area_e5um2_asap7"], b["delay_ps_asap7"], b["cells_asap7"], b["unit_depth"],
                                  b["repair"]["buffers"], b["repair"]["netlist_sha256"][:16]),
                                 (area, delay, cells, depth, bufs, sha))
                self.assertEqual(b["legality"]["table_reads_outside"], 0)
                self.assertEqual(b["liberty_sha256"], lib.sha256)
                if mapped:
                    m = b["mapped"]
                    self.assertTrue(m["available"], m.get("reason"))
                    self.assertEqual((m["area_e5um2_asap7_mapped_v1"], m["mapped_delay_asap7_v1"], m["mapped_cells_asap7_v1"]),
                                     mapped)

    def test_bit_identical_across_processes_and_hash_seeds(self):
        outs = []
        d = tempfile.mkdtemp(prefix="ppa-asap7-det-")
        try:
            for k, seed in enumerate(("0", "12345")):
                j = os.path.join(d, f"r{k}.json")
                env = dict(os.environ, PYTHONHASHSEED=seed, SVGOLF_ASAP7_LIB=REAL_DIR)
                r = subprocess.run([sys.executable, os.path.join(HERE, "ppa.py"), "--pdk", "asap7",
                                    os.path.join(SVGOLF, "tasks/arbiter/reference/rr_mask.sv"), "--task",
                                    os.path.join(SVGOLF, "tasks/arbiter"), "--seq", "--json", j,
                                    "--repaired-netlist", os.path.join(d, f"r{k}.v")],
                                   capture_output=True, text=True, env=env, cwd=d if k else HERE)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                with open(j, "rb") as fh, open(os.path.join(d, f"r{k}.v"), "rb") as fv:
                    outs.append((fh.read(), fv.read()))
        finally:
            shutil.rmtree(d, ignore_errors=True)
        self.assertEqual(outs[0], outs[1])


if __name__ == "__main__":
    unittest.main(verbosity=2)
