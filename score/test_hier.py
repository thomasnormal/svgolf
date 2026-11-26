#!/usr/bin/env python3.12
"""Tests for score/hier.py, the composed ASAP7 score (hierarchy kept).

    python3.12 score/test_hier.py

The netlist reader, the clock ports, the instance counts, the cut of a module at its child instances and the
hierarchy rule run on hand-written netlists (always). The flow tests (the pinned passes with the hierarchy kept on small
designs, composed against the flat score) need the rating build of Yosys, pyslang and the pinned asap7 files, and are
SKIPPED without them.
"""
import os
import shutil
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import hier  # noqa: E402
import ppa  # noqa: E402
import score  # noqa: E402

A7 = ppa.Pins(ppa.pdk_paths("asap7")[0])
REAL_DIR = ppa.find_liberty(None, A7)
HAVE_LIB = os.path.isdir(REAL_DIR) and all(os.path.isfile(os.path.join(REAL_DIR, f["file"])) for f in A7.lib_files)


def have_flow():
    if shutil.which(score.yosys_bin()) is None:
        return False
    try:
        import pyslang  # noqa: F401
    except ImportError:
        return False
    return True


needs_flow = unittest.skipUnless(HAVE_LIB and have_flow(), "needs the pinned asap7 files, Yosys and pyslang")

# a netlist as `write_verilog -noattr -noexpr` writes one: a top with two instances of a registered leaf, a leaf
# with logic on its output, and a block of the SRAM catalogue
NETLIST = r"""
module \$paramod\leaf\W=s32'00000000000000000000000000000010 (clk, d, q);
  wire _0_;
  input clk;
  wire clk;
  input [1:0] d;
  wire [1:0] d;
  output [1:0] q;
  wire [1:0] q;
  \$_XOR_  _1_ (
    .A(d[0]),
    .B(d[1]),
    .Y(_0_)
  );
  \$_DFF_P_  _2_ (
    .C(clk),
    .D(_0_),
    .Q(q[0])
  );
  \$_DFF_P_  _3_ (
    .C(clk),
    .D(d[1]),
    .Q(q[1])
  );
endmodule

module comb(a, y);
  input [1:0] a;
  wire [1:0] a;
  output y;
  wire y;
  \$_AND_  _0_ (
    .A(a[0]),
    .B(a[1]),
    .Y(y)
  );
endmodule

module top(clk, a, y, z);
  wire [1:0] _0_;
  wire _1_;
  wire [15:0] _2_;
  input clk;
  wire clk;
  input [1:0] a;
  wire [1:0] a;
  output [1:0] y;
  wire [1:0] y;
  output z;
  wire z;
  \$_NAND_  _5_ (
    .A(_2_[0]),
    .B(a[0]),
    .Y(_1_)
  );
  \$_DFF_P_  _6_ (
    .C(clk),
    .D(_1_),
    .Q(z)
  );
  \$paramod\leaf\W=s32'00000000000000000000000000000010  _3_ (
    .clk(clk),
    .d(a),
    .q(_0_)
  );
  \$paramod\leaf\W=s32'00000000000000000000000000000010  _4_ (
    .clk(clk),
    .d({ _0_[1], 1'h0 }),
    .q(y)
  );
  srambank_64x4x16_6t122 _7_ (
    .ADDRESS({ 6'h00, a }),
    .banksel(_1_),
    .clk(clk),
    .dataout(_2_),
    .read(1'h1),
    .wd(16'h0000),
    .write(1'h0)
  );
endmodule
"""
LEAF = r"$paramod\leaf\W=s32'00000000000000000000000000000010"


def without(text, name):
    """The netlist without module `name` and without its instances."""
    a = text.index(f"module {name}(")
    b = text.index("endmodule", a) + len("endmodule")
    return text[:a] + text[b:]


class Reading(unittest.TestCase):
    def setUp(self):
        self.table, _ = hier.sram_table()
        self.mods = hier.read_netlist(without(NETLIST, "comb"))

    def test_the_modules_their_gates_and_their_children(self):
        self.assertEqual(sorted(self.mods), [LEAF, "top"])
        top = self.mods["top"]
        self.assertEqual([(k, len(p)) for k, _, p in top.gates], [("$_NAND_", 3), ("$_DFF_P_", 3)])
        self.assertEqual([k for k, _, _ in top.children], [LEAF, LEAF, "srambank_64x4x16_6t122"])
        self.assertEqual(top.children[1][2]["d"], ["_0_[1]", "0"])
        self.assertEqual(top.children[2][2]["ADDRESS"], ["0"] * 6 + ["a[1]", "a[0]"])
        self.assertEqual(hier.show(LEAF), "leaf")

    def test_the_clock_ports_and_the_instance_counts(self):
        self.assertEqual(hier.clock_ports(self.mods, self.table), {LEAF: {"clk"}, "top": {"clk"}})
        counts, blocks = hier.instance_counts(self.mods, self.table, "top")
        self.assertEqual((counts, blocks), ({LEAF: 2, "top": 1}, {"srambank_64x4x16_6t122": 1}))

    def test_the_cut_replaces_every_child_pin_by_a_port(self):
        clocks = hier.clock_ports(self.mods, self.table)
        cut = hier.cut_text(self.mods["top"], self.mods, self.table, clocks)
        nl = ppa.parse_netlist(cut)
        ins = sum(1 for _, d, _ in nl.ports if d == "input")
        outs = sum(1 for _, d, _ in nl.ports if d == "output")
        # top's own 2 inputs + the children's outputs (2 + 2 + 16); top's own 2 outputs + the children's
        # non-constant, non-clock input bits (2 + 1 + 2 address bits + banksel)
        self.assertEqual((ins, outs), (2 + 20, 2 + 6))
        self.assertEqual([g.kind for g in nl.gates], ["$_NAND_", "$_DFF_P_"])
        self.assertNotIn("srambank", cut)

    def test_the_rule_holds_here(self):
        self.assertEqual(hier.rule_findings(self.mods, self.table, "top"), [])

    def test_an_unknown_cell_is_refused(self):
        text = without(NETLIST, "comb").replace("srambank_64x4x16_6t122", "srambank_64x4x17_6t122")
        with self.assertRaises(hier.HierError) as cm:
            hier.compose(text, "top", lib=object(), pins=object())
        self.assertIn("neither a module of the design nor a block of the SRAM catalogue", str(cm.exception))


class Rule(unittest.TestCase):
    def setUp(self):
        self.table, _ = hier.sram_table()

    def findings(self, text):
        return hier.rule_findings(hier.read_netlist(text), self.table, "top")

    def test_an_output_driven_by_logic_is_refused_below_the_top(self):
        text = NETLIST.replace("endmodule\n\nmodule top", "endmodule\n\nmodule top", 1)
        text = text.replace("  srambank_64x4x16_6t122 _7_ (", "  comb _8_ (\n    .a(a),\n    .y(_2_[3])\n  );\n"
                            "  srambank_64x4x16_6t122 _7_ (").replace(".dataout(_2_),", ".dataout({ _2_[15:4], _2_[2:0] }),")
        # (the block now drives 15 bits; the netlist need not be legal Verilog for the rule's reading)
        bad = self.findings(text.replace("{ _2_[15:4], _2_[2:0] }", "_2_[14:0]"))
        self.assertEqual(len(bad), 1)
        self.assertIn("module comb: output `y` is driven by logic", bad[0])

    def test_a_child_input_driven_by_logic_is_refused(self):
        text = without(NETLIST, "comb").replace(".d({ _0_[1], 1'h0 }),", ".d({ _0_[1], _1_ }),")
        bad = self.findings(text)
        self.assertEqual(len(bad), 1)
        self.assertIn("input `d` of its instance of leaf is driven by logic", bad[0])

    def test_logic_in_front_of_a_catalogue_block_is_allowed(self):
        text = without(NETLIST, "comb")
        self.assertIn(".banksel(_1_)", text)             # _1_ is the NAND's output
        self.assertEqual(self.findings(text), [])

    def test_the_tops_outputs_are_not_judged_here(self):
        """The top's outputs are the task's (Moore outputs are the clocked rules' business)."""
        text = without(NETLIST, "comb").replace("    .Q(z)\n", "    .Q(_2_[9])\n").replace(
            "endmodule\n", "", 0)
        text = text.replace("  \\$_NAND_  _5_ (\n    .A(_2_[0]),\n    .B(a[0]),\n    .Y(_1_)\n  );",
                            "  \\$_NAND_  _5_ (\n    .A(_2_[0]),\n    .B(a[0]),\n    .Y(_1_)\n  );\n  assign z = _1_;")
        self.assertEqual(self.findings(text), [])


DESIGN = """
module top #(parameter int K = 3) (input logic clk, input logic [7:0] a, output logic [7:0] y);
  logic [8*(K+1)-1:0] m;
  logic [7:0] a_r;
  always_ff @(posedge clk) a_r <= a ^ 8'h5a;
  assign m[7:0] = a_r;
  for (genvar i = 0; i < K; i++) begin : g
    leaf u (.clk(clk), .d(m[8*i +: 8]), .q(m[8*(i+1) +: 8]));
  end
  assign y = m[8*K +: 8];
endmodule
module leaf (input logic clk, input logic [7:0] d, output logic [7:0] q);
  always_ff @(posedge clk) q <= d * 8'd3 + 8'd1;
endmodule
"""
BAD_OUTPUT = DESIGN.replace("always_ff @(posedge clk) q <= d * 8'd3 + 8'd1;", "assign q = d * 8'd3 + 8'd1;")
BAD_INPUT = DESIGN.replace(".d(m[8*i +: 8])", ".d(m[8*i +: 8] + 8'd1)")
WITH_SRAM = """
module top (input logic clk, input logic we, input logic [7:0] a, input logic [15:0] d, output logic [15:0] q);
  srambank_64x4x16_6t122 m (.clk(clk), .ADDRESS(a ^ 8'h0f), .wd(d), .banksel(1'b1), .read(~we), .write(we),
                            .dataout(q));
endmodule
"""


@needs_flow
class Flow(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.mkdtemp(prefix="svgolf-hier-test-")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.work, ignore_errors=True)

    def design(self, name, text):
        d = os.path.join(self.work, name)
        os.makedirs(d)
        p = os.path.join(d, "design.sv")
        with open(p, "w") as fh:
            fh.write(text)
        return p, d

    def test_the_composed_area_is_instances_times_own_cells(self):
        sv, d = self.design("ok", DESIGN)
        cols = hier.score_design([sv], "top", {"K": 3}, os.path.join(d, "h"))
        rows = {r["module"]: r for r in cols["modules"]}
        self.assertEqual({m: r["instances"] for m, r in rows.items()}, {"top": 1, "leaf": 3})
        self.assertEqual(cols["area_e5um2"], rows["top"]["area_e5um2"] + 3 * rows["leaf"]["area_e5um2"])
        self.assertEqual(cols["flops"], 8 + 3 * 8)
        self.assertEqual(cols["module_period_ps"], max(r["period_ps"] for r in rows.values()))
        self.assertEqual(cols["slowest_module"], "leaf")
        self.assertEqual((cols["version"], cols["sram"], cols["flow"]["rating_build"]),
                         (hier.VERSION, [], score.is_rating_build(score.yosys_bin())))
        # the same design at another size: only the count changes
        cols5 = hier.score_design([sv], "top", {"K": 5}, os.path.join(d, "h5"))
        self.assertEqual(cols5["area_e5um2"], rows["top"]["area_e5um2"] + 5 * rows["leaf"]["area_e5um2"])
        # against the flat score of the same design: the areas agree within the buffers at the cut pins
        net, _ = hier.synthesize([sv], "top", {"K": 3}, os.path.join(d, "f"), flat=True)
        with open(net) as fh:
            flat = hier.flat_period(fh.read(), "top")
        self.assertEqual(flat["flops"], cols["flops"])
        self.assertLessEqual(abs(flat["period_ps"] - cols["module_period_ps"]), 0.25 * cols["module_period_ps"])

    def test_the_hierarchy_rule_is_checked_on_the_netlist(self):
        for name, text, want in (("out", BAD_OUTPUT, "module leaf: output `q` is driven by logic"),
                                 ("in", BAD_INPUT, "input `d` of its instance of leaf is driven by logic")):
            with self.subTest(name=name):
                sv, d = self.design(name, text)
                with self.assertRaises(hier.RuleError) as cm:
                    hier.score_design([sv], "top", {"K": 2}, os.path.join(d, "h"))
                self.assertIn(want, str(cm.exception))

    def test_a_catalogue_block_is_its_table_area(self):
        sv, d = self.design("sram", WITH_SRAM)
        cols = hier.score_design([sv], "top", {}, os.path.join(d, "h"))
        self.assertEqual(cols["sram"], [{"block": "srambank_64x4x16_6t122", "instances": 1, "area_e5um2": 24914304,
                                         "words": 256, "width": 16}])
        self.assertEqual(cols["sram_bits"], 4096)
        self.assertEqual(cols["area_e5um2"], cols["cells_area_e5um2"] + 24914304)
        self.assertGreater(cols["cells_area_e5um2"], 0)             # the address logic and the inverter

    def test_the_scripts_differ_from_the_pinned_ones_in_one_line_each(self):
        def body(path):
            with open(path) as fh:
                return [ln for ln in fh.read().splitlines() if not ln.startswith("#")]
        canon, hcanon = body(score.CANON_SCRIPT), body(hier.CANON_HIER)
        self.assertEqual([ln for ln in canon if ln not in hcanon], ["flatten -noscopeinfo"])
        self.assertEqual([ln for ln in hcanon if ln not in canon], ["setattr -mod -set keep_hierarchy 1 *"])
        seq, hseq = body(score.FLOWS["seq"][0]), body(hier.SEQ_HIER)
        self.assertEqual([ln for ln in seq if ln not in hseq], ["tee -q -o @LTP@ ltp -noff"])
        self.assertEqual([ln for ln in hseq if ln not in seq], [])


if __name__ == "__main__":
    unittest.main()
