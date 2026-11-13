#!/usr/bin/env python3.12
"""The post-synthesis check's loop rule (check/postsynth.py `comb_loops`, in `reread_check`) and the netlist lint's
waiver of Verilator's UNOPTFLAT (`NETLIST_WNO`), 2026-11-13.

Yosys merges flip-flops with equal next-state functions and writes the merged bits as assigns between bits of one
vector (`assign { q[2], q[0] } = { q[3], q[1] };`). Verilator's UNOPTFLAT looks at whole vectors and called that a
combinational loop, so the netlist lint (every warning fatal) refused correct designs. Now a loop is refused BIT BY
BIT on Yosys's `insbuf` view of the netlist before Verilator runs, and UNOPTFLAT is waived.

MUST PASS (the alias):
  * ALIAS_SV, two registers with equal next-state functions whose bits interleave on the output, synthesized by the
    pinned clocked flow (score.py `--seq`): the netlist assigns bits of `q` from other bits of `q`; Verilator's lint
    with UNOPTFLAT fatal refuses it ("Circular combinational logic"), the loop rule finds no loop, the netlist
    re-reads as the scored one, the model builds, and it computes the registers' values cycle by cycle.
  * hand-written netlists with no loop of bits: the same alias written by hand, gates that write one bit of a vector
    from another (a loop of the vector, not of a bit), and feedback through a flip-flop; each also builds.
MUST FAIL (a real loop, refused by `reread_check` before anything is simulated, the message naming its bits):
  * two gates feeding each other through two bits of one vector (what UNOPTFLAT refused before, and must still be
    refused), a gate that reads its own output, a loop of assigns alone, a loop through two wires, a loop through a
    submodule (every cell that is not the flip-flop counts as combinational), and a loop inside a submodule.
Plus `_cycles` on small graphs (self-loop, two components, a DAG).

Needs Yosys (`yosys`, or $SVGOLF_YOSYS, and `yosys-config`), Verilator and a C++ compiler; skipped with a message
where they are not on PATH.

    python3.12 tests/checker/test_postsynth_loops.py
"""

import os
import re
import shutil
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
import postsynth  # noqa: E402
import score  # noqa: E402

HAVE_YOSYS = bool(shutil.which(os.environ.get("SVGOLF_YOSYS") or "yosys")) and bool(shutil.which("yosys-config"))
HAVE_VERILATOR = bool(shutil.which("verilator")) and bool(shutil.which("make"))

# Two registers with equal next-state functions (both load `d`), their bits interleaved on the output: Yosys keeps
# one flip-flop per bit pair and writes the other bit of `q` as an assign from it.
ALIAS_SV = """module alias2 (
  input  logic       clk,
  input  logic [1:0] d,
  output logic [3:0] q
);
  logic [1:0] r1, r2;
  always_ff @(posedge clk) begin
    r1 <= d;
    r2 <= d;
  end
  assign q = {r1[1], r2[1], r1[0], r2[0]};
endmodule
"""

PASS = {
    # the merged flip-flops of ALIAS_SV, written by hand
    "p_alias": """module t(clk, d, q);
  input clk; input [1:0] d; output [3:0] q;
  \\$_DFF_P_ r1 (.C(clk), .D(d[0]), .Q(q[1]));
  \\$_DFF_P_ r3 (.C(clk), .D(d[1]), .Q(q[3]));
  assign { q[2], q[0] } = { q[3], q[1] };
endmodule
""",
    # gates that write one bit of `w` from another bit of `w`: a loop of the vector, none of a bit
    "p_vector": """module t(a, b, y);
  input a; input b; output y;
  wire [2:0] w;
  \\$_NOT_ g0 (.A(a), .Y(w[0]));
  \\$_AND_ g1 (.A(w[0]), .B(b), .Y(w[1]));
  \\$_XOR_ g2 (.A(w[1]), .B(w[0]), .Y(w[2]));
  assign y = w[2];
endmodule
""",
    # feedback through a flip-flop (a toggle): a loop of the circuit, not a combinational one
    "p_flop": """module t(clk, q);
  input clk; output q;
  wire n;
  \\$_DFF_P_ r (.C(clk), .D(n), .Q(q));
  \\$_NOT_ g (.A(q), .Y(n));
endmodule
""",
}

FAIL = {
    # two gates feeding each other through two bits of one vector
    "f_vector": ("""module t(a, b, y);
  input a; input b; output y;
  wire [1:0] w;
  \\$_AND_ g1 (.A(a), .B(w[1]), .Y(w[0]));
  \\$_OR_ g2 (.A(w[0]), .B(b), .Y(w[1]));
  assign y = w[1];
endmodule
""", ["`w[0]`", "`w[1]`"]),
    # a gate that reads its own output
    "f_self": ("""module t(a, s, y);
  input a; input s; output y;
  \\$_MUX_ m (.A(y), .B(a), .S(s), .Y(y));
endmodule
""", ["`y`"]),
    # a loop of assigns alone
    "f_assigns": ("""module t(a, y);
  input a; output y;
  wire u, v;
  assign u = v;
  assign v = u;
  \\$_AND_ g (.A(a), .B(u), .Y(y));
endmodule
""", ["`u`", "`v`"]),
    # a loop through two wires
    "f_wires": ("""module t(a, y);
  input a; output y;
  wire u, v;
  \\$_NAND_ g1 (.A(a), .B(v), .Y(u));
  \\$_NAND_ g2 (.A(a), .B(u), .Y(v));
  assign y = v;
endmodule
""", ["`u`", "`v`"]),
    # a loop through a submodule: its output reads its input
    "f_sub": ("""module sub(i, o);
  input i; output o;
  \\$_NOT_ g (.A(i), .Y(o));
endmodule
module t(a, y);
  input a; output y;
  wire u, v;
  sub s (.i(v), .o(u));
  \\$_XOR_ g (.A(a), .B(u), .Y(v));
  assign y = v;
endmodule
""", ["`u`", "`v`"]),
    # a loop inside a submodule
    "f_inner": ("""module sub(i, o);
  input i; output o;
  wire w;
  \\$_OR_ g1 (.A(i), .B(o), .Y(w));
  \\$_BUF_ g2 (.A(w), .Y(o));
endmodule
module t(a, y);
  input a; output y;
  sub s (.i(a), .o(y));
endmodule
""", ["`o`", "`w`", "of module `sub`"]),
}


def reread(text, top, work):
    path = os.path.join(work, "netlist.v")
    with open(path, "w") as fh:
        fh.write(text)
    return path, postsynth.reread_netlist(path, top, work)


def lint_build(netlist, top, ins, outs, work, tag, wno=None):
    """`vl_build` of the netlist with the plain harness (the lint and the C++ build, as postsynth runs them);
    `wno` replaces NETLIST_WNO."""
    with mock.patch.object(postsynth, "NETLIST_WNO", postsynth.NETLIST_WNO if wno is None else wno):
        return postsynth.vl_build([netlist, postsynth.simcells()], top, {}, ins, outs, work, tag, 300)


class Cycles(unittest.TestCase):
    def test_small_graphs(self):
        self.assertEqual(postsynth._cycles({1: {1}}), [[1]])
        self.assertEqual(postsynth._cycles({1: {2}, 2: {3}}), [])
        self.assertEqual(postsynth._cycles({1: {2}, 2: {1, 3}, 3: {4}, 4: {3}, 5: {1}}), [[3, 4], [1, 2]])
        self.assertEqual(postsynth._cycles({i: {i + 1} for i in range(20000)} | {20000: {0}}),
                         [list(range(20001))])           # iterative: no recursion limit at netlist size


@unittest.skipUnless(HAVE_YOSYS, "needs Yosys (`yosys` and `yosys-config`)")
class HandNetlists(unittest.TestCase):
    def setUp(self):
        self.work = tempfile.mkdtemp(prefix="svgolf-loops-")
        self.addCleanup(shutil.rmtree, self.work, ignore_errors=True)

    def test_no_loop_of_bits_passes_the_rule(self):
        for name, text in PASS.items():
            with self.subTest(name):
                d = os.path.join(self.work, name)
                os.makedirs(d)
                _, (_, _, _, _, drivers) = reread(text, "t", d)
                self.assertEqual(postsynth.comb_loops(drivers), [])

    def test_a_real_loop_is_refused_naming_its_bits(self):
        for name, (text, words) in FAIL.items():
            with self.subTest(name):
                d = os.path.join(self.work, name)
                os.makedirs(d)
                path, (cells, depth, _, _, drivers) = reread(text, "t", d)
                found = postsynth.comb_loops(drivers)
                self.assertEqual(len(found), 1, found)
                self.assertIn("it has a combinational loop through", found[0])
                for w in words:
                    self.assertIn(w, found[0])
                # in reread_check, before the gate count and before Verilator
                sres = {"gates": {re.sub(r"^\\?\$_(\w+?)_$", r"\1", c): n for c, n in cells.items()},
                        "depth": depth}
                with self.assertRaises(postsynth.Reject) as cm:
                    postsynth.reread_check(path, "t", sres, d)
                self.assertIn("the netlist is refused before it is simulated: it has a combinational loop",
                              str(cm.exception))

    @unittest.skipUnless(HAVE_VERILATOR, "needs Verilator and make")
    def test_what_passes_the_rule_builds(self):
        for name, text in PASS.items():
            with self.subTest(name):
                d = os.path.join(self.work, name)
                os.makedirs(d)
                path, (_, _, design, _, _) = reread(text, "t", d)
                ports = postsynth.netlist_ports(design, "t")
                ins = sorted((n, w) for k, n, w in ports if k == "input")
                outs = sorted((n, w) for k, n, w in ports if k == "output")
                exe, _, err = lint_build(path, "t", ins, outs, d, "net")
                self.assertIsNone(err)
                self.assertTrue(exe and os.path.isfile(exe))


@unittest.skipUnless(HAVE_YOSYS and HAVE_VERILATOR, "needs Yosys, Verilator and make")
class MergedFlipFlops(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.work = tempfile.mkdtemp(prefix="svgolf-alias-")
        sv = os.path.join(cls.work, "alias2.sv")
        with open(sv, "w") as fh:
            fh.write(ALIAS_SV)
        cls.netlist = os.path.join(cls.work, "netlist.v")
        cls.sres = score.score([sv], "alias2", {}, flow="seq", netlist_out=cls.netlist)
        with open(cls.netlist) as fh:
            cls.text = fh.read()

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.work, ignore_errors=True)

    def ports(self, design):
        ports = postsynth.netlist_ports(design, "alias2")
        return ([p for p in sorted((n, w) for k, n, w in ports if k == "input") if p[0] != "clk"],
                sorted((n, w) for k, n, w in ports if k == "output"))

    def test_the_flow_merges_the_registers_into_bit_aliases(self):
        self.assertEqual(self.sres["gates"], {"DFF_P": 2})
        self.assertRegex(self.text, r"assign \{ q\[\d\], q\[\d\] \} = \{ q\[\d\], q\[\d\] \};")

    def test_the_vector_lint_calls_it_circular(self):
        d = tempfile.mkdtemp(dir=self.work)
        design, _ = postsynth.reread_check(self.netlist, "alias2", self.sres, d)
        ins, outs = self.ports(design)
        exe, _, err = lint_build(self.netlist, "alias2", [("clk", 1)] + ins, outs, d, "old",
                                 wno=tuple(w for w in postsynth.NETLIST_WNO if w != "UNOPTFLAT"))
        self.assertIsNone(exe)
        self.assertIn("UNOPTFLAT", err)
        self.assertIn("Circular combinational logic", err)

    def test_it_passes_and_computes_the_registers(self):
        d = tempfile.mkdtemp(dir=self.work)
        design, drivers = postsynth.reread_check(self.netlist, "alias2", self.sres, d)
        self.assertEqual(postsynth.comb_loops(drivers), [])
        ins, outs = self.ports(design)
        harness = postsynth.harness_cpp(ins, outs, postsynth.CLOCKED_HARNESS, clk="clk", done="false")
        exe, _, err = postsynth.vl_build([self.netlist, postsynth.simcells()], "alias2", {}, ins, outs, d,
                                         "clocked", 300, harness=harness, xflags=postsynth.VL_X_CLOCKED)
        self.assertIsNone(err)
        ds = [0, 1, 2, 3, 2, 1, 3, 0]
        vp = os.path.join(d, "lines.hex")
        with open(vp, "w") as fh:
            fh.write("".join(f"E {v:x}\n" for v in ds))
        r = subprocess.run([exe, vp, "1", "0", "0"], capture_output=True, text=True, timeout=60)
        self.assertEqual(r.returncode, 0, r.stderr)
        rows = [ln.split() for ln in r.stdout.splitlines()]
        self.assertEqual(rows[-1], ["END", str(len(ds))])
        want = [f"{v >> 1 & 1}{v >> 1 & 1}{v & 1}{v & 1}" for v in ds]      # q = {d[1], d[1], d[0], d[0]}
        self.assertEqual([x[1] for x in rows[:-1]], want)


if __name__ == "__main__":
    unittest.main(verbosity=2)
