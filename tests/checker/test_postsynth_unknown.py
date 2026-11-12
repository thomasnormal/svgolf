#!/usr/bin/env python3.12
"""The post-synthesis check's rule for unknown-valued constants in the scored netlist (check/postsynth.py
`unknown_bits`, `unknown_message`), on hand-written netlists re-read by Yosys exactly as `reread_check` re-reads the
scored one (`reread_netlist`: the netlist, `simcells.v` as a library, `hierarchy -top`, `write_json`). Decided
2026-11-11: an unknown constant is refused where something reads it, as Yosys's own reader of the netlist shows,
and accepted where nothing does.

MUST PASS:
  * n_ok      `w[0] = 1'hx`, read by nothing (the shape Yosys leaves where it removed an unused register bit):
              no readers; the unread net is `w`, bit 0.
MUST FAIL (each with its one reader):
  * n_out     an output bit tied to 1'hx                    -> the output `y`, bit 0
  * n_alias   v1 = v2 = v3 = w[0] = 1'hx, read by an AND gate -> the `$_AND_` cell `g1`, pin B
  * n_dff     a flip-flop's D tied to 1'hx                  -> the `$_DFF_P_` cell `r`, pin D
  * n_lit     an AND gate with .B(1'hx), no net at all      -> the `$_AND_` cell `g1`, pin B
  * n_masked  an AND gate with .A(1'b0), .B(1'hx)           -> pin B (refused although the 0 masks it: fail closed)
  * n_z       an output bit tied to 1'hz                    -> the output `y`
  * n_hier    a submodule that ties and reads an x          -> the `$_AND_` cell `g` of module `sub`, pin B (every
              module is read, not only the top one)
plus the ports, read from the same JSON (`netlist_ports`), and the message's parts (the names, the declaration line,
the readers, "and N more"). Also (Readers.test_every_reader_is_found, each in x and z where it has a literal): a pin of
an inout (a submodule's), an inout port, a pin of unknown direction (a cell type nothing defines), an output whose
range does not start at 0 (`[5:2]`) or ascends (`[0:3]`), named by its declared index, and z on a flip-flop's D and
clock, a mux select and a submodule pin. The message names the bit of a wide pin that holds a literal, and names only
the wires something reads (`read_unknown`, from the `insbuf` view).

FAIL SAFE (decided 2026-11-12; `reread_check`, before the gate count): where Yosys's first view could hide an unknown
value, the netlist is refused, in x and z alike:
  * a bit with two drivers, one of them unknown: `y = 0` then `y = x`, `y = 1` then `y = x` (the first view shows the
    known one), the reverse orders, a signal and an x, a gate output and an x on one wire, read or not;
  * a box: a module the netlist marks `(* blackbox *)` (whose body Yosys's view drops), `(* blackbox = 0 *)`,
    `(* whitebox *)`; a cell of a type nothing defines; a cell Yosys made from an expression.
And what must still pass it: the shapes above with one driver per bit, and an empty submodule (read with
`-noblackbox`, so Yosys does not turn it into a box).

THE NAMING RUN (`unknown_names`, made only when the check refuses): the scored run's sources, gating, point and flow
again, with the design's names kept; on the counter fixture that leaves an unread bit
(tests/seq_counter/never_loaded/ok_unread_bit.sv) it names `t[0]`; a run that fails gives None, and the refusal then
has no such clause; end to end, a refusal of `_example` whose output bit is an x (the gate bypassed, as the attacks'
`postsynth_alone` runs) names the source's bits.

Needs Yosys (`yosys`, or $SVGOLF_YOSYS, and `yosys-config`); skipped with a message where it is not on PATH.

    python3.12 tests/checker/test_postsynth_unknown.py
"""

import os
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import postsynth  # noqa: E402

HAVE_YOSYS = bool(shutil.which(os.environ.get("SVGOLF_YOSYS") or "yosys")) and bool(shutil.which("yosys-config"))

NETLISTS = {
    "n_ok": """module t(a, y);
  input [1:0] a; output y;
  wire [1:0] w;
  assign w[0] = 1'hx;
  assign w[1] = a[1];
  \\$_AND_ g1 (.A(a[0]), .B(w[1]), .Y(y));
endmodule
""",
    "n_out": """module t(a, y);
  input [1:0] a; output [1:0] y;
  assign y[0] = 1'hx;
  assign y[1] = a[1];
endmodule
""",
    "n_alias": """module t(a, y);
  input a; output y;
  wire v1, v2, v3;
  wire [1:0] w;
  assign w[0] = 1'hx;
  assign w[1] = a;
  assign v1 = w[0];
  assign v2 = v1;
  assign v3 = v2;
  \\$_AND_ g1 (.A(a), .B(v3), .Y(y));
endmodule
""",
    "n_dff": """module t(clk, a, y);
  input clk; input a; output y;
  wire q;
  \\$_DFF_P_ r (.C(clk), .D(1'hx), .Q(q));
  \\$_AND_ g (.A(q), .B(a), .Y(y));
endmodule
""",
    "n_lit": """module t(a, y);
  input a; output y;
  \\$_AND_ g1 (.A(a), .B(1'hx), .Y(y));
endmodule
""",
    "n_masked": """module t(a, y);
  input a; output y;
  \\$_AND_ g (.A(1'b0), .B(1'hx), .Y(y));
endmodule
""",
    "n_z": """module t(a, y);
  input a; output y;
  assign y = 1'bz;
endmodule
""",
    "n_hier": """module sub(i, o);
  input i; output o;
  wire [1:0] w;
  assign w[0] = 1'hx;
  assign w[1] = i;
  \\$_AND_ g (.A(i), .B(w[0]), .Y(o));
endmodule
module t(a, y);
  input a; output y;
  sub u (.i(a), .o(y));
endmodule
""",
}

SUB2 = """module sub2(i, o);
  input [1:0] i; output o;
  \\$_AND_ g (.A(i[0]), .B(i[1]), .Y(o));
endmodule
"""
# Each in x and in z (V is the literal): name -> netlist text.
BOTH = {
    "n_offset": """module t(a, y);
  input a; output [5:2] y;
  assign y[2] = a; assign y[3] = V; assign y[4] = a; assign y[5] = a;
endmodule
""",
    "n_upto": """module t(a, y);
  input a; output [0:3] y;
  assign y[0] = a; assign y[1] = V; assign y[2] = a; assign y[3] = a;
endmodule
""",
    "n_inout_port": """module t(a, io);
  input a; inout io;
  assign io = V;
endmodule
""",
    "n_inout_pin": """module sub(io);
  inout io;
endmodule
module t(a, y);
  input a; output y;
  sub u (.io(V));
  assign y = a;
endmodule
""",
    "n_unknown_type": """module t(a, y);
  input a; output y;
  \\$_FOO_ g (.A(a), .B(V), .Y(y));
endmodule
""",
    "n_d_lit": """module t(clk, a, y);
  input clk; input a; output y;
  wire q;
  \\$_DFF_P_ r (.C(clk), .D(V), .Q(q));
  \\$_AND_ g (.A(q), .B(a), .Y(y));
endmodule
""",
    "n_clk_lit": """module t(clk, a, y);
  input clk; input a; output y;
  wire q;
  \\$_DFF_P_ r (.C(V), .D(a), .Q(q));
  \\$_AND_ g (.A(q), .B(a), .Y(y));
endmodule
""",
    "n_mux_select": """module t(a, b, y);
  input a, b; output y;
  \\$_MUX_ m (.A(a), .B(b), .S(V), .Y(y));
endmodule
""",
    "n_sub_pin": SUB2 + """module t(a, y);
  input a; output y;
  sub2 u (.i({V, a}), .o(y));
endmodule
""",
    "n_concat": SUB2 + """module t(a, y);
  input a; output y;
  sub2 u (.i({a, V}), .o(y));
endmodule
""",
    "n_mixed": """module t(a, y);
  input a; output [1:0] y;
  wire dead;
  assign dead = V;
  assign y[0] = V;
  assign y[1] = a;
endmodule
""",
    # FAIL SAFE: two drivers of one bit, one of them unknown (refused by reread_check)
    "c_0_then_x": """module t(a, y);
  input a; output y;
  assign y = 1'b0;
  assign y = V;
endmodule
""",
    "c_1_then_x": """module t(a, y);
  input a; output y;
  assign y = 1'b1;
  assign y = V;
endmodule
""",
    "c_x_then_0": """module t(a, y);
  input a; output y;
  assign y = V;
  assign y = 1'b0;
endmodule
""",
    "c_sig_then_x": """module t(a, y);
  input a; output y;
  assign y = a;
  assign y = V;
endmodule
""",
    "c_known_and_x_on_wire": """module t(a, y);
  input a; output y;
  wire w;
  assign w = 1'b0;
  assign w = V;
  \\$_AND_ g (.A(a), .B(w), .Y(y));
endmodule
""",
    "c_gate_and_x_unread": """module t(a, y);
  input a; output y;
  wire w;
  \\$_AND_ g (.A(a), .B(a), .Y(w));
  assign w = V;
  assign y = a;
endmodule
""",
    "c_known_and_alias_of_x": """module t(a, y);
  input a; output y;
  wire w, v;
  assign w = V;
  assign v = 1'b0;
  assign v = w;
  \\$_AND_ g (.A(a), .B(v), .Y(y));
endmodule
""",
}
for _name, _text in BOTH.items():
    NETLISTS[_name + "_x"] = _text.replace("V", "1'hx")
    NETLISTS[_name + "_z"] = _text.replace("V", "1'hz")
# FAIL SAFE: what the rule cannot look into (refused by reread_check)
NETLISTS.update({
    "o_blackbox": """(* blackbox *)
module sub(i, o);
  input i; output o;
  \\$_AND_ g (.A(i), .B(1'hx), .Y(o));
endmodule
module t(a, y);
  input a; output y;
  sub u (.i(a), .o(y));
endmodule
""",
    "o_blackbox_0": """(* blackbox = 0 *)
module sub(i, o);
  input i; output o;
  \\$_AND_ g (.A(i), .B(1'hx), .Y(o));
endmodule
module t(a, y);
  input a; output y;
  sub u (.i(a), .o(y));
endmodule
""",
    "o_whitebox": """(* whitebox *)
module sub(i, o);
  input i; output o;
  \\$_AND_ g (.A(i), .B(i), .Y(o));
endmodule
module t(a, y);
  input a; output y;
  sub u (.i(a), .o(y));
endmodule
""",
    "o_expression": """module t(a, b, y);
  input a, b; output y;
  assign y = a & b;
endmodule
""",
    "o_empty_sub": """module sub(i);
  input i;
endmodule
module t(a, y);
  input a; output y;
  sub u (.i(a));
  \\$_NOT_ g (.A(a), .Y(y));
endmodule
""",
})


@unittest.skipUnless(HAVE_YOSYS, "needs Yosys (yosys and yosys-config on PATH)")
class Readers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="svgolf-x-")
        cls.design, cls.views = {}, {}
        for name, text in NETLISTS.items():
            work = os.path.join(cls.tmp, name)
            os.makedirs(work)
            netlist = os.path.join(work, "netlist.v")
            with open(netlist, "w") as fh:
                fh.write(text)
            cls.views[name] = postsynth.reread_netlist(netlist, "t", work)
            cls.design[name] = cls.views[name][2]

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def bits(self, name):
        return postsynth.unknown_bits(self.design[name], "t")

    def test_an_unread_unknown_is_accepted(self):
        unread, readers = self.bits("n_ok")
        self.assertEqual(readers, [])
        self.assertEqual([(u["net"], u["bits"], u["value"]) for u in unread], [("w", [0], "x")])
        self.assertEqual(unread[0]["line"], 3)          # the declaration `wire [1:0] w;`, from the src attribute
        self.assertIsNone(postsynth.unknown_message(unread, readers))
        self.assertIn("ties `w[0]` to an unknown value that nothing reads", postsynth.unread_note(unread))

    def test_every_reader_is_found(self):
        want = {
            "n_out": [{"kind": "port", "port": "y", "direction": "output", "width": 2, "bits": [0]}],
            "n_alias": [{"kind": "cell", "cell": "g1", "type": "$_AND_", "pin": "B", "bits": []}],
            "n_dff": [{"kind": "cell", "cell": "r", "type": "$_DFF_P_", "pin": "D", "bits": []}],
            "n_lit": [{"kind": "cell", "cell": "g1", "type": "$_AND_", "pin": "B", "bits": []}],
            "n_masked": [{"kind": "cell", "cell": "g", "type": "$_AND_", "pin": "B", "bits": []}],
            "n_z": [{"kind": "port", "port": "y", "direction": "output", "width": 1, "bits": [0]}],
            "n_hier": [{"kind": "cell", "cell": "g", "type": "$_AND_", "pin": "B", "bits": [], "module": "sub"}],
        }
        for v in ("x", "z"):
            want.update({
                f"n_offset_{v}": [{"kind": "port", "port": "y", "direction": "output", "width": 4, "bits": [3]}],
                f"n_upto_{v}": [{"kind": "port", "port": "y", "direction": "output", "width": 4, "bits": [1]}],
                f"n_inout_port_{v}": [{"kind": "port", "port": "io", "direction": "inout", "width": 1, "bits": [0]}],
                f"n_inout_pin_{v}": [{"kind": "cell", "cell": "u", "type": "sub", "pin": "io", "bits": []}],
                f"n_unknown_type_{v}": [{"kind": "cell", "cell": "g", "type": "$_FOO_", "pin": "B", "bits": []}],
                f"n_d_lit_{v}": [{"kind": "cell", "cell": "r", "type": "$_DFF_P_", "pin": "D", "bits": []}],
                f"n_clk_lit_{v}": [{"kind": "cell", "cell": "r", "type": "$_DFF_P_", "pin": "C", "bits": []}],
                f"n_mux_select_{v}": [{"kind": "cell", "cell": "m", "type": "$_MUX_", "pin": "S", "bits": []}],
                f"n_sub_pin_{v}": [{"kind": "cell", "cell": "u", "type": "sub2", "pin": "i", "bits": [1]}],
                f"n_concat_{v}": [{"kind": "cell", "cell": "u", "type": "sub2", "pin": "i", "bits": [0]}],
            })
        for name, readers in want.items():
            with self.subTest(name):
                self.assertEqual(self.bits(name)[1], readers)
                self.assertIsNotNone(postsynth.unknown_message(*self.bits(name)))

    def test_the_hierarchy_is_read_whole(self):
        """The top module alone shows no x in n_hier: only reading every module finds the submodule's reader."""
        top_only = {"modules": {"t": self.design["n_hier"]["modules"]["t"]}}
        self.assertEqual(postsynth.unknown_bits(top_only, "t"), ([], []))
        unread, readers = self.bits("n_hier")
        self.assertEqual([(u["module"], u["net"], u["bits"]) for u in unread], [("sub", "w", [0])])
        self.assertIn("the `$_AND_` cell `g` of module `sub` (pin B)", postsynth.unknown_message(unread, readers))

    def test_the_messages(self):
        out = postsynth.unknown_message(*self.bits("n_out"))
        self.assertTrue(out.startswith("the netlist ties `y[0]` (declared at netlist line 2) to an unknown value, and "
                                       "it is read by the output `y` (bit 0): a 2-state simulation would read it as a "
                                       "fixed 0 or 1"), out)
        self.assertTrue(out.endswith("check.py --keep keeps the netlist (the result's `postsynth_dir`)"), out)
        alias = postsynth.unknown_message(*self.bits("n_alias"))
        self.assertIn("the `$_AND_` cell `g1` (pin B)", alias)
        for net in ("`v1`", "`v2`", "`v3`", "`w[0]`"):
            self.assertIn(net, alias)
        self.assertIn("declared at netlist lines 3 and 4", alias)
        lit = postsynth.unknown_message(*self.bits("n_lit"))
        self.assertEqual(lit, "the netlist reads an unknown value: the `$_AND_` cell `g1` has an unknown value on pin "
                              "B: a 2-state simulation would read it as a fixed 0 or 1. check.py --keep keeps the "
                              "netlist (the result's `postsynth_dir`)")
        self.assertIn("ties `y` (declared at netlist line 2)", postsynth.unknown_message(*self.bits("n_z")))
        # at most five readers, then "and N more"
        many = [{"kind": "cell", "cell": f"g{k}", "type": "$_AND_", "pin": "B", "bits": []} for k in range(8)]
        w = [{"net": "w", "width": 1, "bits": [0], "value": "x", "line": 3}]
        self.assertIn("read by the `$_AND_` cell `g0` (pin B), the `$_AND_` cell `g1` (pin B), ",
                      postsynth.unknown_message(w, many))
        self.assertIn("`g4` (pin B) and 3 more:", postsynth.unknown_message(w, many))
        self.assertIn("`g4` has an unknown value on pin B and 3 more:", postsynth.unknown_message([], many))
        wide = [{"kind": "port", "port": "y", "direction": "output", "width": 16, "bits": list(range(16))}]
        self.assertIn("read by the output `y` (bits 0, 1, 2, 3, 4 and 11 more):", postsynth.unknown_message(w, wide))
        # the declared index of a range that does not start at 0, or ascends
        self.assertIn("ties `y[3]` (declared at netlist line 2) to an unknown value, and it is read by the output `y` "
                      "(bit 3)", postsynth.unknown_message(*self.bits("n_offset_x")))
        self.assertIn("ties `y[1]` (declared at netlist line 2) to an unknown value, and it is read by the output `y` "
                      "(bit 1)", postsynth.unknown_message(*self.bits("n_upto_z")))
        # a literal on a wide pin: the bit is named
        self.assertIn("the `sub2` cell `u` has an unknown value on pin i, bit 0:",
                      postsynth.unknown_message(*self.bits("n_concat_x")))
        self.assertIn("the `sub2` cell `u` has an unknown value on pin i, bit 1:",
                      postsynth.unknown_message(*self.bits("n_sub_pin_z")))
        self.assertIn("has an unknown value on pin B:", lit)          # a one-bit pin: no bit

    def test_the_message_names_only_the_wires_something_reads(self):
        """`dead` holds an x that nothing reads; `y[0]` holds one the output reads. Yosys's first view gives the two
        constants no identity, so without `read_unknown` both wires are named; with it (the `insbuf` view), only
        `y[0]`. Through aliases the named wires are those on the way to the reader (n_alias: all four)."""
        for v in ("x", "z"):
            unread, readers = self.bits(f"n_mixed_{v}")
            self.assertEqual(sorted(u["net"] for u in unread), ["dead", "y"])
            read = postsynth.read_unknown(self.views[f"n_mixed_{v}"][4], "t")
            self.assertEqual(read, {(None, "y", 0)})
            named = postsynth.unknown_message(unread, readers, read=read)
            self.assertTrue(named.startswith("the netlist ties `y[0]` (declared at netlist line 2) to an unknown "
                                             "value, and it is read by the output `y` (bit 0)"), named)
            self.assertNotIn("dead", named)
            self.assertIn("`dead`", postsynth.unknown_message(unread, readers))
        alias = postsynth.unknown_message(*self.bits("n_alias"), read=postsynth.read_unknown(self.views["n_alias"][4]))
        for net in ("`v1`", "`v2`", "`v3`", "`w[0]`"):
            self.assertIn(net, alias)
        # a literal on a pin and an unread wire: no wire is named
        lit = postsynth.read_unknown(self.views["n_lit"][4], "t")
        self.assertEqual(lit, set())
        self.assertTrue(postsynth.unknown_message([{"net": "w", "width": 1, "bits": [0], "value": "x", "line": 3}],
                                                  self.bits("n_lit")[1], read=lit)
                        .startswith("the netlist reads an unknown value: the `$_AND_` cell `g1` has"))

    def refuse(self, name):
        """reread_check on the netlist with a score result made of its own counts (so that the gate comparison would
        pass): the Reject's message."""
        cells, depth = self.views[name][0], self.views[name][1]
        gates = {}
        for c, n in cells.items():
            m = postsynth.re.fullmatch(r"\\?\$_(\w+?)_", c)
            gates[m.group(1) if m else c] = n
        work = os.path.join(self.tmp, name)
        with self.assertRaises(postsynth.Reject) as cm:
            postsynth.reread_check(os.path.join(work, "netlist.v"), "t", {"gates": gates, "depth": depth,
                                                                         "flow": "seq"}, work)
        return cm.exception.msg

    def passes(self, name):
        cells, depth = self.views[name][0], self.views[name][1]
        gates = {}
        for c, n in cells.items():
            m = postsynth.re.fullmatch(r"\\?\$_(\w+?)_", c)
            gates[m.group(1) if m else c] = n
        work = os.path.join(self.tmp, name)
        return postsynth.reread_check(os.path.join(work, "netlist.v"), "t", {"gates": gates, "depth": depth,
                                                                            "flow": "seq"}, work)

    def test_two_drivers_of_a_bit_with_an_unknown_one_are_refused(self):
        """F1: Yosys's first view keeps one driver of a bit: `y = 0; y = x` shows y = 0, read or not."""
        for v in ("x", "z"):
            with self.subTest(v=v):
                self.assertEqual(self.bits(f"c_0_then_x_{v}"), ([], []))       # what the first view alone says
                self.assertEqual(self.bits(f"c_known_and_x_on_wire_{v}")[1], [])
                for name, net in (("c_0_then_x", "`y` (declared at netlist line 2)"),
                                  ("c_1_then_x", "`y` (declared at netlist line 2)"),
                                  ("c_x_then_0", "`y` (declared at netlist line 2)"),
                                  ("c_sig_then_x", "`y` (declared at netlist line 2)"),
                                  ("c_known_and_x_on_wire", "`w` (declared at netlist line 3)"),
                                  ("c_gate_and_x_unread", "`w` (declared at netlist line 3)"),
                                  ("c_known_and_alias_of_x", "`v` (declared at netlist line 3)"),
                                  ("n_inout_port", "`io` (declared at netlist line 2)")):
                    msg = self.refuse(f"{name}_{v}")
                    self.assertTrue(msg.startswith("the netlist is refused before it is simulated: it drives "
                                                   f"{net} from more than one place, and one of the drivers is an "
                                                   "unknown value"), (name, msg))
                    self.assertTrue(msg.endswith("check.py --keep keeps the netlist (the result's `postsynth_dir`)"))
                    self.assertEqual(len(postsynth.conflicting_drivers(self.views[f"{name}_{v}"][4])), 1)

    def test_what_the_rule_cannot_look_into_is_refused(self):
        """F2: a box module (its body is not in Yosys's view), a cell type nothing defines, a cell made from an
        expression."""
        self.assertEqual(self.bits("o_blackbox"), ([], []))                    # the first view shows no x at all
        for name, part in (("o_blackbox", "it defines module `sub` with the attribute `blackbox` (the check cannot "
                                          "see what a box computes)"),
                           ("o_blackbox_0", "it defines module `sub` with the attribute `blackbox`"),
                           ("o_whitebox", "it defines module `sub` with the attribute `whitebox`"),
                           ("n_unknown_type_x", "its `$_FOO_` cell `g` is neither a gate of Yosys's cell library nor "
                                                "a module the netlist defines"),
                           ("o_expression", "it has a `$and` cell that Yosys made from an expression at netlist line 3 "
                                            "(the pinned flow writes gate instances only)")):
            with self.subTest(name):
                msg = self.refuse(name)
                self.assertTrue(msg.startswith("the netlist is refused before it is simulated: " + part), msg)

    def test_one_driver_per_bit_and_an_empty_submodule_pass_it(self):
        for name in ("n_ok", "n_alias", "n_out", "n_dff", "n_hier", "n_mixed_x", "n_concat_z", "n_inout_pin_x",
                     "o_empty_sub"):
            with self.subTest(name):
                design, drivers = self.passes(name)
                self.assertEqual(postsynth.conflicting_drivers(drivers), [])
                self.assertEqual(postsynth.opaque_parts(self.views[name][3], design), [])

    def test_the_ports_come_from_the_same_reading(self):
        self.assertEqual(postsynth.netlist_ports(self.design["n_out"], "t"), {("input", "a", 2), ("output", "y", 2)})
        self.assertEqual(postsynth.netlist_ports(self.design["n_dff"], "t"),
                         {("input", "clk", 1), ("input", "a", 1), ("output", "y", 1)})
        with self.assertRaises(postsynth.Reject):
            postsynth.netlist_ports(self.design["n_out"], "nosuch")


FIXTURE = os.path.join(SVGOLF, "tests", "seq_counter", "never_loaded", "ok_unread_bit.sv")
X_OUT = """module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [N-1:0] w;
  assign w = {a[N-1:1] & b[N-1:1], 1'bx};
  assign y = w;
endmodule
"""


@unittest.skipUnless(HAVE_YOSYS, "needs Yosys (yosys and yosys-config on PATH)")
class NamingRun(unittest.TestCase):
    def test_it_names_the_source_bit(self):
        sres = {"sources": [{"path": FIXTURE}], "gated": True, "top": "cnt", "params": {"N": 8}, "flow": "seq"}
        self.assertEqual(postsynth.unknown_names(sres), ["t[0]"])

    def test_a_failed_run_names_nothing_and_the_clause_goes(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = os.path.join(tmp, "bad.sv")
            with open(bad, "w") as fh:
                fh.write("module cnt (input logic a, output logic y); assign y = ; endmodule\n")
            sres = {"sources": [{"path": bad}], "gated": False, "top": "cnt", "params": {}, "flow": "seq"}
            self.assertIsNone(postsynth.unknown_names(sres))
        self.assertIsNone(postsynth.unknown_names({"sources": [], "top": "cnt", "params": {}}))
        readers = [{"kind": "port", "port": "y", "direction": "output", "width": 1, "bits": [0]}]
        unread = [{"net": "y", "width": 1, "bits": [0], "value": "x", "line": 2}]
        plain = postsynth.unknown_message(unread, readers)
        self.assertNotIn("keeps your signal names", plain)
        named = postsynth.unknown_message(unread, readers, ["t[0]", "u"])
        self.assertIn("as a fixed 0 or 1. In a run that keeps your signal names, the unknown bits are `t[0]` and `u`. "
                      "check.py --keep keeps the netlist", named)

    @unittest.skipUnless(os.path.isfile(postsynth.SVEVAL), "needs the built svgolf-eval (lake build)")
    def test_a_refusal_names_the_source_bits(self):
        with tempfile.TemporaryDirectory() as tmp:
            sv = os.path.join(tmp, "band.sv")
            with open(sv, "w") as fh:
                fh.write(X_OUT)
            with self.assertRaises(postsynth.Reject) as cm:
                postsynth.check_design(os.path.join(SVGOLF, "tasks", "_example"), sv, tmp, gate=False, mode="light")
        msg = cm.exception.info["record"]["netlist_unknown_constant"]
        self.assertIn("is read by the output `y` (bit 0)", msg)
        self.assertIn("In a run that keeps your signal names, the unknown bits are ", msg)
        self.assertIn("`y[0]`", msg.split("keeps your signal names")[1])


if __name__ == "__main__":
    unittest.main(verbosity=1)
