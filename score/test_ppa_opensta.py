#!/usr/bin/env python3.12
"""ppa.py's STA against OpenSTA, golden numbers recorded below (svGolf, 11/04 STA gap study).

OpenSTA (OpenROAD in the docker image openroad/orfs:26Q4-262-g3ff0197f0, `OPENSTA_TCL` below) timed the netlists this file
builds (`netlists()`), on the pinned liberty, with svGolf's own assumptions: no wires (`set_load 0` on every net), 10 fF on
every output bit, every input an ideal 50 ps ramp at 0. Its numbers are recorded in GOLD_JSON below (ns, 6 decimals as OpenSTA prints
them) and ppa.py must reproduce every one within TOL_NS:

* `CellArcTest`: every timing arc of 46 cells (the families a golfer may hand-instantiate: fa/ha, maj3, xor3/xnor3, a21oi/o21ai,
  mux2i/mux2/mux4, nand4/nor4, the a2111/o2111/a222 compounds, the ten A0' gates, buffers and inverters, _0 to _16 drive
  strengths, clkbuf/clkinv/dlygate): one instance with every input at the ramp, then one more per (output, input pin) with
  that pin driven by the first instance (its slew and load) x 3 copies; every cell output pin's arrival, both edges. The
  multi-output fa/ha, the clkbuf/clkinv and the dlygate cells are admitted for the measurement (the policy refuses them
  today: `cell_class`; PLAN4's hand-instantiation rule admits every cell with a function).
* `HandBuiltTest`: structural designs (a two-input-gate adder as A0' writes them, an fa_1 ripple, maj3+xor3, an a21oi/o21ai
  carry chain, a mux2i tree, a nand4/nor4 tree): the latest arrival and every output bit's, both edges, under the A1' setup
  (ideal ramps) and the A0' setup, whose input driver is ppa.py's `drive_arrival`: OpenSTA timed the same netlist with ONE
  explicit buf_1 instance per input (`explicit=True`), which is what ppa.py's driver means. The OpenSTA runs used buf_1
  (`DRIVE`), the drive of sky130_a0_v2; sky130_a0_v3 drives the inputs by the task's `input_drive` (default buf_8), every
  allowed cell through the same `drive_arrival`, so buf_1 stands for all of them here.
* `DriverConventionTest`: OpenSTA's own `set_driving_cell buf_1` adds only the driver's load-dependent delay,
  delay(load) - delay(0); ppa.py adds the whole cell delay. Both recorded, the difference is the extrapolated zero-load delay
  (buf_1 at the 50 ps ramp: 58.7 ps for a rising input, 72.8 ps for a falling one).
* `EdgeLoadTest`: a load pin's rise_capacitance times a rising edge, its fall_capacitance a falling one (the defect this
  file was written for: ppa.py read `capacitance`, 0.5% to 2.8% off OpenSTA on the references); max_capacitance is checked
  on the larger edge (OpenSTA flags the case below, `capacitance` would not).
* `ClockedTest`: a register-to-register period (dfxtp_1 clock-to-Q at the Q load per edge, its D pin per edge, setup).

Re-record: `python3.12 score/test_ppa_opensta.py --emit DIR` writes every netlist and `jobs.txt`; run OPENSTA_TCL on each
(env NET, TOP, MODE in {ramp, drive, clocked}, OUT) inside the image, then `--record DIR` prints GOLD_JSON.
"""
import json
import math
import os
import sys
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import ppa  # noqa: E402

P = "sky130_fd_sc_hd__"
PINS = ppa.Pins()
LIB_PATH = ppa.find_liberty(None, PINS)
HAVE_LIB = os.path.isfile(LIB_PATH)
REQUIRE_LIB = os.environ.get("SVGOLF_PPA_REQUIRE_LIB") == "1"
needs_lib = unittest.skipUnless(HAVE_LIB or REQUIRE_LIB, f"the pinned sky130 liberty is absent ({LIB_PATH})")
TOL_NS = 2e-6          # OpenSTA prints 6 decimals of a ns; ppa.py's doubles agree to the last printed digit
DRIVE = P + "buf_1"    # the input drive of the OpenSTA runs (explicit buf_1 instances, `set_driving_cell buf_1`)

OPENSTA_TCL = r"""
read_lef /OpenROAD-flow-scripts/flow/platforms/sky130hd/lef/sky130_fd_sc_hd.tlef
read_lef /OpenROAD-flow-scripts/flow/platforms/sky130hd/lef/sky130_fd_sc_hd_merged.lef
read_liberty /w/lib.lib
read_verilog $::env(NET)
link_design $::env(TOP)
set mode $::env(MODE)
if {$mode eq "clocked"} {
  create_clock -name clk -period 10 [get_ports clk]
  set_clock_transition 0.05 [all_clocks]
  set ins [lsearch -all -inline -not [all_inputs] [get_ports clk]]
} else {
  create_clock -name clk -period 10
  set ins [all_inputs]
}
set_input_delay 0 -clock clk $ins
set_output_delay 0 -clock clk [all_outputs]
if {$mode eq "drive"} {
  set_driving_cell -lib_cell sky130_fd_sc_hd__buf_1 -pin X -input_transition_rise 0.05 -input_transition_fall 0.05 $ins
} else {
  set_input_transition 0.05 $ins
}
set_load 0.010 [all_outputs]
set_load 0 [get_nets *]
set fh [open $::env(OUT) w]
puts $fh "T\t[format %.6f [expr {10.0 - [sta::worst_slack -max]}]]"
foreach p [all_outputs] { puts $fh "PO\t[get_full_name $p]\t[get_property $p slack_max_rise]\t[get_property $p slack_max_fall]" }
foreach c [get_cells *] {
  foreach pin [get_pins -of_objects $c -filter "direction==output"] {
    puts $fh "PIN\t[get_full_name $pin]\t[get_property $pin arrival_max_rise]\t[get_property $pin arrival_max_fall]"
  }
}
close $fh
report_check_types -max_capacitance -violators -digits 6 > $::env(OUT).cap
exit
"""

COVER_KINDS = ["fa_1", "fa_2", "ha_1", "maj3_1", "maj3_4", "xor3_1", "xor3_4", "xnor3_1", "a21oi_1", "a21oi_2", "a21oi_4",
               "o21ai_0", "o21ai_1", "o21ai_4", "a21boi_0", "o21bai_1", "a31oi_1", "o22ai_1", "a2111oi_0", "o2111ai_1", "a222oi_1",
               "mux2i_1", "mux2i_4", "mux2_1", "mux4_1", "nand4_1", "nand4_4", "nor4_1", "nor4_4", "and4bb_1",
               "inv_1", "inv_16", "buf_1", "buf_16", "nand2_1", "nor2_1", "and2_1", "or2_1", "xor2_1", "xnor2_1", "nor2b_1",
               "nand2b_1", "clkbuf_1", "clkinv_2", "dlygate4sd1_1", "nand2_8"]
COVER_FANOUT = 3


# --------------------------------------------------------------------------------------------- the netlists
class _M:
    def __init__(self, name):
        self.name, self.ins, self.outs, self.body, self.wires, self.k = name, [], [], [], [], 0

    def i(self, n):
        self.ins.append(n)
        return n

    def w(self):
        self.k += 1
        self.wires.append(f"t{self.k}")
        return f"t{self.k}"

    def cell(self, kind, **pins):
        self.k += 1
        self.body.append(f"  {P}{kind} g{self.k} (" + ", ".join(f".{p}({n})" for p, n in pins.items()) + ");")

    def o(self, n, net):
        self.outs.append(n)
        self.body.append(f"  assign {n} = {net};")

    def text(self, explicit=False, keep=()):
        """The module; `explicit`: one buf_1 instance in front of every input but `keep` (ppa.py's input driver as a cell)."""
        body, wires = list(self.body), list(self.wires)
        if explicit:
            ren = {x: f"{x}_b" for x in self.ins if x not in keep}
            import re
            body = [re.sub(r"\(([A-Za-z_][A-Za-z0-9_]*)\)", lambda m: f"({ren.get(m.group(1), m.group(1))})", b)
                    if not b.startswith("  assign") else re.sub(r"= ([A-Za-z_][A-Za-z0-9_]*);",
                                                                 lambda m: f"= {ren.get(m.group(1), m.group(1))};", b)
                    for b in body]
            wires += list(ren.values())
            body = [f"  {P}buf_1 ib_{x} (.A({x}), .X({y}));" for x, y in ren.items()] + body
        return "\n".join([f"module {self.name}({', '.join(self.ins + self.outs)});"] + [f"  input {x};" for x in self.ins]
                         + [f"  output {x};" for x in self.outs] + [f"  wire {x};" for x in wires] + body + ["endmodule", ""])


def cover(lib):
    """Every kind of COVER_KINDS: u1 with every input a primary input; for each output o and input pin q, COVER_FANOUT copies
    of u2 with q <- u1.o and the other pins primary inputs; every cell output an output bit."""
    m = _M("cover")
    for k, short in enumerate(COVER_KINDS):
        c = lib.cell(P + short)
        pi = {p: m.i(f"i{k}_{p}") for p in c.inputs}
        n1 = {}
        for o in c.outputs:
            n1[o] = f"w{k}_{o}"
            m.wires.append(n1[o])
        m.body.append(f"  {P}{short} c{k}_u1 (" + ", ".join([f".{p}({pi[p]})" for p in c.inputs]
                                                          + [f".{o}({n1[o]})" for o in c.outputs]) + ");")
        for o in c.outputs:
            m.o(f"y{k}_{o}", n1[o])
            for q in c.inputs:
                for f in range(COVER_FANOUT):
                    outs = {o2: f"y{k}_{o}_{q}_{f}_{o2}" for o2 in c.outputs}
                    m.outs += list(outs.values())
                    m.body.append(f"  {P}{short} c{k}_{o}_{q}_{f} (" + ", ".join(
                        [f".{p}({n1[o] if p == q else pi[p]})" for p in c.inputs] + [f".{o2}({outs[o2]})" for o2 in c.outputs])
                        + ");")
    return m


def hand():
    ms = []
    m = _M("gates2")                        # an 8-bit adder of two-input _1 gates, as A0' writes them
    c = m.i("cin")
    for b in range(8):
        a, bb = m.i(f"a{b}"), m.i(f"b{b}")
        p, g, nc, s = m.w(), m.w(), m.w(), m.w()
        m.cell("xor2_1", A=a, B=bb, X=p)
        m.cell("nand2_1", A=a, B=bb, Y=g)
        if b % 2 == 0:
            m.cell("xnor2_1", A=p, B=c, Y=s)
            t = m.w()
            m.cell("nor2b_1", A=c, B_N=p, Y=t)            # !c & p ... a mix of the A0' inventory
            u = m.w()
            m.cell("nand2_1", A=p, B=c, Y=u)
            m.cell("nand2_1", A=u, B=g, Y=nc)
            sx = m.w()
            m.cell("inv_1", A=s, Y=sx)
            m.o(f"s{b}", sx)
            m.o(f"z{b}", t)
        else:
            m.cell("xor2_1", A=p, B=c, X=s)
            m.cell("mux2_1", A0=g, A1=c, S=p, X=nc)
            m.o(f"s{b}", s)
        c = nc
    m.o("cout", c)
    ms.append(m)
    m = _M("fa_ripple")                     # 16-bit ripple of fa_1 (multi-output)
    c = m.i("cin")
    for b in range(16):
        a, bb = m.i(f"a{b}"), m.i(f"b{b}")
        co, so = m.w(), m.w()
        m.cell("fa_1", A=a, B=bb, CIN=c, COUT=co, SUM=so)
        m.o(f"s{b}", so)
        c = co
    m.o("cout", c)
    ms.append(m)
    m = _M("maj_xor3")
    c = m.i("cin")
    for b in range(16):
        a, bb = m.i(f"a{b}"), m.i(f"b{b}")
        co, so = m.w(), m.w()
        m.cell("maj3_1", A=a, B=bb, C=c, X=co)
        m.cell("xor3_1", A=a, B=bb, C=c, X=so)
        m.o(f"s{b}", so)
        c = co
    m.o("cout", c)
    ms.append(m)
    m = _M("aoi_oai")
    c = m.i("cin")
    for b in range(16):
        g, p = m.i(f"g{b}"), m.i(f"p{b}")
        co, so = m.w(), m.w()
        m.cell("a21oi_1" if b % 2 == 0 else "o21ai_1", A1=p, A2=c, B1=g, Y=co)
        m.cell("xnor2_1", A=p, B=c, Y=so)
        m.o(f"s{b}", so)
        c = co
    m.o("cout", c)
    ms.append(m)
    m = _M("mux2i_tree")
    lvl = [m.i(f"d{j}") for j in range(32)]
    sel = [m.i(f"s{j}") for j in range(5)]
    for L in range(5):
        nxt = []
        for j in range(0, len(lvl), 2):
            y = m.w()
            m.cell("mux2i_1", A0=lvl[j], A1=lvl[j + 1], S=sel[L], Y=y)
            nxt.append(y)
        lvl = nxt
    m.o("y", lvl[0])
    ms.append(m)
    m = _M("nand4_tree")
    lvl = [m.i(f"x{j}") for j in range(64)]
    for kind in ("nand4_1", "nor4_1", "nand4_4"):
        nxt = []
        for j in range(0, len(lvl), 4):
            y = m.w()
            m.cell(kind, A=lvl[j], B=lvl[j + 1], C=lvl[j + 2], D=lvl[j + 3], Y=y)
            nxt.append(y)
        lvl = nxt
    m.o("y", lvl[0])
    ms.append(m)
    return ms


def cap_probe():
    """xor2_1 driving 33 inv_1 inputs: 33 x 2.302 fF (`capacitance`) = 75.97 fF is within its max_capacitance 76.914 fF,
    33 x 2.390 fF (rise_capacitance) = 78.87 fF is not."""
    m = _M("cap_probe")
    a, b = m.i("a"), m.i("b")
    x = m.w()
    m.cell("xor2_1", A=a, B=b, X=x)
    for j in range(33):
        y = m.w()
        m.cell("inv_1", A=x, Y=y)
        m.o(f"y{j}", y)
    return m


def clocked():
    """Two dfxtp_1 flops, a Q -> nand2/xor2/maj3 cone -> D loop, an input into the cone and an output (repaired-netlist style:
    ppa.read_repaired reads the dfxtp_1 cells)."""
    m = _M("clocked")
    clk, a = m.i("clk"), m.i("a")
    q0, q1, d0, d1, t1, t2, t3 = (m.w() for _ in range(7))
    m.cell("dfxtp_1", CLK=clk, D=d0, Q=q0)
    m.cell("dfxtp_1", CLK=clk, D=d1, Q=q1)
    m.cell("nand2_1", A=q0, B=a, Y=t1)
    m.cell("xor2_1", A=t1, B=q1, X=t2)
    m.cell("maj3_1", A=t2, B=q0, C=a, X=t3)
    m.cell("inv_2", A=t3, Y=d0)
    m.cell("xnor2_1", A=t2, B=q0, Y=d1)
    m.o("y", t3)
    return m


def netlists(lib):
    """{name: (module, text, MODE)} of every netlist OpenSTA timed."""
    out = {}
    out["cover"] = (cover(lib), None, "ramp")
    for m in hand():
        out[m.name] = (m, None, "ramp")
        out[m.name + "_x"] = (m, "explicit", "ramp")
    d = _M("driver")                        # one input into one inv_1
    a = d.i("a")
    y = d.w()
    d.cell("inv_1", A=a, Y=y)
    d.o("y", y)
    out["driver"] = (d, None, "drive")
    out["driver_x"] = (d, "explicit", "ramp")
    out["cap_probe"] = (cap_probe(), None, "ramp")
    ck = clocked()
    out["clocked_x"] = (ck, "explicit", "clocked")
    return {k: (m, m.text(explicit=(e == "explicit"), keep=("clk",)), mode) for k, (m, e, mode) in out.items()}


# --------------------------------------------------------------------------------------------- ppa.py's side
ADMITTED = ("multi-output", "clock", "delay")      # cells with a function that the policy refuses today


def _admit_function_cells():
    """The fa/ha, clkbuf/clkinv and dlygate cells weighed as logic: the measurement covers every cell with a function
    (PLAN4's hand-instantiation rule); `ppa.cell_class` refuses them today."""
    orig = ppa.cell_class
    return mock.patch.object(ppa, "cell_class", lambda n, prefix=P: "logic" if orig(n, prefix) in ADMITTED
                             else orig(n, prefix))


def weigh(lib, text, drive):
    """(T, {output bit: {edge: arrival}}, {inst/PIN: {edge: arrival}}) of ppa.py's STA (A1''s reading: extrapolation as
    OpenSTA does, so a read outside a grid is compared too, never clamped)."""
    with _admit_function_cells():
        nl = ppa.parse_netlist(text)
        d = ppa.Design(nl, lib, PINS)
    T, _ = d.sta(PINS.pi_slew_ns, PINS.po_load_pf, None, (), ppa.input_drive_cell(lib, PINS, DRIVE) if drive else None, ppa.A1_EXTRAPOLATES)
    po = {nl.port_bit(p, k): {e: d.arr[(nl.resolve(n), e)][0] for e in "rf" if (nl.resolve(n), e) in d.arr}
          for p, k, n in nl.po}
    pins = {f"{d.names[i]}/{pin}": {e: d.arr[(net, e)][0] for e in "rf" if (net, e) in d.arr}
            for net, (i, pin) in d.driver.items()}
    return T, po, pins


# --------------------------------------------------------------------------------------------- the goldens (OpenSTA)
GOLD = None        # filled from GOLD_JSON below


def _gold():
    global GOLD
    if GOLD is None:
        GOLD = json.loads(GOLD_JSON)
    return GOLD


class _Base(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not HAVE_LIB:
            raise unittest.SkipTest(f"the pinned sky130 liberty is absent ({LIB_PATH})")
        cls.lib = ppa.Liberty(LIB_PATH, PINS)
        cls.nets = netlists(cls.lib)

    def close(self, got, want, what):
        self.assertTrue(math.isfinite(got) and abs(got - want) <= TOL_NS, f"{what}: ppa.py {got:.7f} ns, OpenSTA {want:.6f} ns")


@needs_lib
class CellArcTest(_Base):
    def test_every_arc_of_the_cover_netlist(self):
        g = _gold()["cover"]
        T, po, pins = weigh(self.lib, self.nets["cover"][1], drive=False)
        self.close(T, g["T"], "cover: latest arrival")
        n = 0
        for pin, edges in g["pins"].items():
            for e, want in edges.items():
                self.close(pins[pin][e], want, f"cover {pin} {e}")
                n += 1
        self.assertGreater(n, 600)

    def test_cover_has_the_families(self):
        for k in ("fa_1", "maj3_1", "xor3_1", "a21oi_1", "o21ai_1", "mux2i_1", "nand4_1", "a21oi_2", "o21ai_4", "mux2i_4",
                  "maj3_4", "inv_16", "buf_16"):
            self.assertIn(k, COVER_KINDS)


@needs_lib
class HandBuiltTest(_Base):
    def check(self, name, drive):
        key = name + ("_x" if drive else "")
        g = _gold()[key]
        T, po, _ = weigh(self.lib, self.nets[name][1], drive=drive)
        self.close(T, g["T"], f"{key}: latest arrival")
        for bit, edges in g["po"].items():
            for e, want in edges.items():
                self.close(po[bit][e], want, f"{key} {bit} {e}")

    def test_ideal_ramps(self):           # flow A1''s setup
        for m in hand():
            with self.subTest(m.name):
                self.check(m.name, drive=False)

    def test_buf_1_driven_inputs(self):   # flow A0''s setup: OpenSTA with one buf_1 instance per input
        for m in hand():
            with self.subTest(m.name):
                self.check(m.name, drive=True)


@needs_lib
class DriverConventionTest(_Base):
    def test_whole_cell_delay_not_set_driving_cell(self):
        g = _gold()
        T, po, pins = weigh(self.lib, self.nets["driver"][1], drive=True)
        self.close(pins["g2/Y"]["f"], g["driver_x"]["pins"]["g2/Y"]["f"], "inv_1 behind an explicit buf_1, falling")
        self.close(pins["g2/Y"]["r"], g["driver_x"]["pins"]["g2/Y"]["r"], "inv_1 behind an explicit buf_1, rising")
        # OpenSTA's set_driving_cell counts delay(load) - delay(0): less by buf_1's extrapolated zero-load delay
        arc = self.lib.cell(P + "buf_1").arcs["X"][0]
        for e, w, ie in (("f", "fall", "r"), ("r", "rise", "f")):       # inv_1: the output edge e follows input edge ie
            zero = arc.tbl["cell_" + {"r": "rise", "f": "fall"}[ie]]._bilinear(PINS.pi_slew_ns, 0.0)
            self.close(pins["g2/Y"][e] - zero, g["driver"]["pins"]["g2/Y"][e], f"set_driving_cell convention, {w}")
            self.assertGreater(zero, 0.05)


@needs_lib
class EdgeLoadTest(_Base):
    def test_rise_and_fall_capacitance(self):
        inv = self.lib.cell(P + "inv_1")
        self.assertEqual((inv.pin_cap["A"], inv.pin_cap_e["A"]), (0.002302, {"r": 0.00239, "f": 0.002214}))

    def test_max_capacitance_on_the_larger_edge(self):
        g = _gold()["cap_probe"]
        self.assertTrue(g["opensta_violation"])        # OpenSTA: report_check_types -max_capacitance -violators
        with _admit_function_cells():
            nl = ppa.parse_netlist(self.nets["cap_probe"][1])
            d = ppa.Design(nl, self.lib, PINS)
        audit = ppa.Audit()
        d.sta(PINS.pi_slew_ns, PINS.po_load_pf, None, (), None, audit)
        d.legality(PINS.po_load_pf, audit, self.lib.default_max_transition)
        self.assertEqual(len(audit.cap), 1, audit.report())
        self.assertIn("xor2_1 g2 driving net t1", audit.cap[0][1])
        x = "t1"
        self.assertLessEqual(d.load_pf(x, PINS.po_load_pf), 0.076914)          # within it at `capacitance`
        self.assertAlmostEqual(d.load_max_pf(x, PINS.po_load_pf), g["load_max"], places=9)


@needs_lib
class ClockedTest(_Base):
    def test_register_to_register_period(self):
        g = _gold()["clocked_x"]
        nl, flops, ties, _ = ppa.read_repaired(clocked().text(), self.lib, PINS)
        q, dn = ppa.cut_flops(nl, flops)
        a = ppa.weigh_cells(nl, q, dn, len(flops), self.lib, PINS, ppa.input_drive_cell(self.lib, PINS, DRIVE), ppa.Audit(), ties=ties)
        self.close(a.t_ns, g["T"], "clocked: period")


# --------------------------------------------------------------------------------------------- re-recording
def _emit(outdir):
    lib = ppa.Liberty(LIB_PATH, PINS)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "jobs.txt"), "w") as jobs:
        for name, (m, text, mode) in netlists(lib).items():
            open(os.path.join(outdir, name + ".v"), "w").write(text)
            jobs.write(f"{name} {name}.v {m.name} {mode}\n")
    open(os.path.join(outdir, "opensta.tcl"), "w").write(OPENSTA_TCL)


def _num(x):
    try:
        v = float(x)
    except ValueError:
        return None
    return v if math.isfinite(v) and abs(v) < 1e20 else None


def _record(outdir):
    lib = ppa.Liberty(LIB_PATH, PINS)
    nets = netlists(lib)
    gold = {}
    for name in nets:
        o = {"T": None, "po": {}, "pins": {}}
        for line in open(os.path.join(outdir, name + ".sta")):
            f = line.rstrip("\n").split("\t")
            if f[0] == "T":
                o["T"] = float(f[1])
            elif f[0] == "PO":
                o["po"][f[1]] = {e: round(10.0 - v, 6) for e, v in zip("rf", map(_num, f[2:4])) if v is not None}
            elif f[0] == "PIN" and not f[1].startswith("ib_"):
                o["pins"][f[1]] = {e: v for e, v in zip("rf", map(_num, f[2:4])) if v is not None}
        if name not in ("cover", "driver", "driver_x"):
            o.pop("pins")
        if name == "cover" or name.startswith("cap_probe") or name.startswith("clocked"):
            o.pop("po")
        if name == "cap_probe":
            cap = open(os.path.join(outdir, name + ".sta.cap")).read()
            o["opensta_violation"] = "VIOLATED" in cap
            with _admit_function_cells():
                nl = ppa.parse_netlist(nets[name][1])
                d = ppa.Design(nl, lib, PINS)
            x = "t1"
            o["load_max"] = d.load_max_pf(x, PINS.po_load_pf)
            o["opensta_cap_report"] = " ".join(cap.split())[:200]
        gold[name] = o
    q = "'" * 3
    print(f"GOLD_JSON = r{q}" + json.dumps(gold, sort_keys=True, separators=(",", ":")) + q)


GOLD_JSON = r'''{"aoi_oai":{"T":2.632041,"po":{"cout":{"f":2.565604,"r":2.372092},"s0":{"f":0.161459,"r":0.254899},"s1":{"f":0.336808,"r":0.396473},"s10":{"f":1.757115,"r":1.833731},"s11":{"f":1.933643,"r":1.993307},"s12":{"f":2.076482,"r":2.153097},"s13":{"f":2.25301,"r":2.312675},"s14":{"f":2.39585,"r":2.472464},"s15":{"f":2.572377,"r":2.632041},"s2":{"f":0.479648,"r":0.556263},"s3":{"f":0.656176,"r":0.71584},"s4":{"f":0.799015,"r":0.87563},"s5":{"f":0.975542,"r":1.035208},"s6":{"f":1.118382,"r":1.194997},"s7":{"f":1.294909,"r":1.354574},"s8":{"f":1.437748,"r":1.514363},"s9":{"f":1.614276,"r":1.673941}}},"aoi_oai_x":{"T":2.741429,"po":{"cout":{"f":2.674994,"r":2.504075},"s0":{"f":0.268079,"r":0.361545},"s1":{"f":0.443954,"r":0.503615},"s10":{"f":1.865893,"r":1.942473},"s11":{"f":2.042391,"r":2.102054},"s12":{"f":2.18558,"r":2.262161},"s13":{"f":2.362079,"r":2.421742},"s14":{"f":2.505268,"r":2.581849},"s15":{"f":2.681767,"r":2.741429},"s2":{"f":0.587142,"r":0.663722},"s3":{"f":0.76364,"r":0.823303},"s4":{"f":0.90683,"r":0.983411},"s5":{"f":1.083328,"r":1.14299},"s6":{"f":1.226518,"r":1.303098},"s7":{"f":1.403016,"r":1.462678},"s8":{"f":1.546205,"r":1.622786},"s9":{"f":1.722704,"r":1.782366}}},"cap_probe":{"T":1.400013,"load_max":0.07887000000000001,"opensta_cap_report":"max capacitance Pin Limit Cap Slack ------------------------------------------------------------------------ g2/X 0.076914 0.078870 -0.001956 (VIOLATED)","opensta_violation":true},"clocked_x":{"T":1.120221},"cover":{"T":2.601059,"pins":{"c0_COUT_A_0/COUT":{"f":1.247097,"r":0.905754},"c0_COUT_A_0/SUM":{"f":1.298608,"r":1.363933},"c0_COUT_A_1/COUT":{"f":1.247097,"r":0.905754},"c0_COUT_A_1/SUM":{"f":1.298608,"r":1.363933},"c0_COUT_A_2/COUT":{"f":1.247097,"r":0.905754},"c0_COUT_A_2/SUM":{"f":1.298608,"r":1.363933},"c0_COUT_B_0/COUT":{"f":1.230178,"r":0.903648},"c0_COUT_B_0/SUM":{"f":1.287305,"r":1.344557},"c0_COUT_B_1/COUT":{"f":1.230178,"r":0.903648},"c0_COUT_B_1/SUM":{"f":1.287305,"r":1.344557},"c0_COUT_B_2/COUT":{"f":1.230178,"r":0.903648},"c0_COUT_B_2/SUM":{"f":1.287305,"r":1.344557},"c0_COUT_CIN_0/COUT":{"f":1.207652,"r":0.910301},"c0_COUT_CIN_0/SUM":{"f":1.264748,"r":1.323561},"c0_COUT_CIN_1/COUT":{"f":1.207652,"r":0.910301},"c0_COUT_CIN_1/SUM":{"f":1.264748,"r":1.323561},"c0_COUT_CIN_2/COUT":{"f":1.207652,"r":0.910301},"c0_COUT_CIN_2/SUM":{"f":1.264748,"r":1.323561},"c0_SUM_A_0/COUT":{"f":1.308211,"r":1.277047},"c0_SUM_A_0/SUM":{"f":1.486172,"r":1.425021},"c0_SUM_A_1/COUT":{"f":1.308211,"r":1.277047},"c0_SUM_A_1/SUM":{"f":1.486172,"r":1.425021},"c0_SUM_A_2/COUT":{"f":1.308211,"r":1.277047},"c0_SUM_A_2/SUM":{"f":1.486172,"r":1.425021},"c0_SUM_B_0/COUT":{"f":1.291881,"r":1.274925},"c0_SUM_B_0/SUM":{"f":1.506033,"r":1.406241},"c0_SUM_B_1/COUT":{"f":1.291881,"r":1.274925},"c0_SUM_B_1/SUM":{"f":1.506033,"r":1.406241},"c0_SUM_B_2/COUT":{"f":1.291881,"r":1.274925},"c0_SUM_B_2/SUM":{"f":1.506033,"r":1.406241},"c0_SUM_CIN_0/COUT":{"f":1.269376,"r":1.281608},"c0_SUM_CIN_0/SUM":{"f":1.506973,"r":1.385241},"c0_SUM_CIN_1/COUT":{"f":1.269376,"r":1.281608},"c0_SUM_CIN_1/SUM":{"f":1.506973,"r":1.385241},"c0_SUM_CIN_2/COUT":{"f":1.269376,"r":1.281608},"c0_SUM_CIN_2/SUM":{"f":1.506973,"r":1.385241},"c0_u1/COUT":{"f":0.690235,"r":0.568519},"c0_u1/SUM":{"f":0.74765,"r":0.939068},"c10_Y_A1_0/Y":{"f":0.66377,"r":0.350714},"c10_Y_A1_1/Y":{"f":0.66377,"r":0.350714},"c10_Y_A1_2/Y":{"f":0.66377,"r":0.350714},"c10_Y_A2_0/Y":{"f":0.673773,"r":0.373862},"c10_Y_A2_1/Y":{"f":0.673773,"r":0.373862},"c10_Y_A2_2/Y":{"f":0.673773,"r":0.373862},"c10_Y_B1_0/Y":{"f":0.607205,"r":0.343851},"c10_Y_B1_1/Y":{"f":0.607205,"r":0.343851},"c10_Y_B1_2/Y":{"f":0.607205,"r":0.343851},"c10_u1/Y":{"f":0.16195,"r":0.544821},"c11_Y_A1_0/Y":{"f":0.946487,"r":0.688415},"c11_Y_A1_1/Y":{"f":0.946487,"r":0.688415},"c11_Y_A1_2/Y":{"f":0.946487,"r":0.688415},"c11_Y_A2_0/Y":{"f":0.918512,"r":0.688058},"c11_Y_A2_1/Y":{"f":0.918512,"r":0.688058},"c11_Y_A2_2/Y":{"f":0.918512,"r":0.688058},"c11_Y_B1_0/Y":{"f":0.96383,"r":0.548158},"c11_Y_B1_1/Y":{"f":0.96383,"r":0.548158},"c11_Y_B1_2/Y":{"f":0.96383,"r":0.548158},"c11_u1/Y":{"f":0.283388,"r":0.628873},"c12_Y_A1_0/Y":{"f":0.71265,"r":0.505921},"c12_Y_A1_1/Y":{"f":0.71265,"r":0.505921},"c12_Y_A1_2/Y":{"f":0.71265,"r":0.505921},"c12_Y_A2_0/Y":{"f":0.685597,"r":0.499454},"c12_Y_A2_1/Y":{"f":0.685597,"r":0.499454},"c12_Y_A2_2/Y":{"f":0.685597,"r":0.499454},"c12_Y_B1_0/Y":{"f":0.71991,"r":0.438032},"c12_Y_B1_1/Y":{"f":0.71991,"r":0.438032},"c12_Y_B1_2/Y":{"f":0.71991,"r":0.438032},"c12_u1/Y":{"f":0.214815,"r":0.492696},"c13_Y_A1_0/Y":{"f":0.669725,"r":0.392998},"c13_Y_A1_1/Y":{"f":0.669725,"r":0.392998},"c13_Y_A1_2/Y":{"f":0.669725,"r":0.392998},"c13_Y_A2_0/Y":{"f":0.638134,"r":0.375998},"c13_Y_A2_1/Y":{"f":0.638134,"r":0.375998},"c13_Y_A2_2/Y":{"f":0.638134,"r":0.375998},"c13_Y_B1_0/Y":{"f":0.668775,"r":0.299948},"c13_Y_B1_1/Y":{"f":0.668775,"r":0.299948},"c13_Y_B1_2/Y":{"f":0.668775,"r":0.299948},"c13_u1/Y":{"f":0.176667,"r":0.539336},"c14_Y_A1_0/Y":{"f":0.976073,"r":0.668188},"c14_Y_A1_1/Y":{"f":0.976073,"r":0.668188},"c14_Y_A1_2/Y":{"f":0.976073,"r":0.668188},"c14_Y_A2_0/Y":{"f":0.971186,"r":0.678489},"c14_Y_A2_1/Y":{"f":0.971186,"r":0.678489},"c14_Y_A2_2/Y":{"f":0.971186,"r":0.678489},"c14_Y_B1_N_0/Y":{"f":0.530863,"r":1.049313},"c14_Y_B1_N_1/Y":{"f":0.530863,"r":1.049313},"c14_Y_B1_N_2/Y":{"f":0.530863,"r":1.049313},"c14_u1/Y":{"f":0.265099,"r":0.653609},"c15_Y_A1_0/Y":{"f":0.724567,"r":0.589092},"c15_Y_A1_1/Y":{"f":0.724567,"r":0.589092},"c15_Y_A1_2/Y":{"f":0.724567,"r":0.589092},"c15_Y_A2_0/Y":{"f":0.698233,"r":0.581099},"c15_Y_A2_1/Y":{"f":0.698233,"r":0.581099},"c15_Y_A2_2/Y":{"f":0.698233,"r":0.581099},"c15_Y_B1_N_0/Y":{"f":0.564161,"r":0.748509},"c15_Y_B1_N_1/Y":{"f":0.564161,"r":0.748509},"c15_Y_B1_N_2/Y":{"f":0.564161,"r":0.748509},"c15_u1/Y":{"f":0.291638,"r":0.50105},"c16_Y_A1_0/Y":{"f":1.002584,"r":0.651888},"c16_Y_A1_1/Y":{"f":1.002584,"r":0.651888},"c16_Y_A1_2/Y":{"f":1.002584,"r":0.651888},"c16_Y_A2_0/Y":{"f":1.00839,"r":0.68985},"c16_Y_A2_1/Y":{"f":1.00839,"r":0.68985},"c16_Y_A2_2/Y":{"f":1.00839,"r":0.68985},"c16_Y_A3_0/Y":{"f":0.995602,"r":0.678316},"c16_Y_A3_1/Y":{"f":0.995602,"r":0.678316},"c16_Y_A3_2/Y":{"f":0.995602,"r":0.678316},"c16_Y_B1_0/Y":{"f":0.906768,"r":0.667858},"c16_Y_B1_1/Y":{"f":0.906768,"r":0.667858},"c16_Y_B1_2/Y":{"f":0.906768,"r":0.667858},"c16_u1/Y":{"f":0.303978,"r":0.730878},"c17_Y_A1_0/Y":{"f":0.928835,"r":0.619357},"c17_Y_A1_1/Y":{"f":0.928835,"r":0.619357},"c17_Y_A1_2/Y":{"f":0.928835,"r":0.619357},"c17_Y_A2_0/Y":{"f":0.895907,"r":0.61651},"c17_Y_A2_1/Y":{"f":0.895907,"r":0.61651},"c17_Y_A2_2/Y":{"f":0.895907,"r":0.61651},"c17_Y_B1_0/Y":{"f":0.932688,"r":0.58549},"c17_Y_B1_1/Y":{"f":0.932688,"r":0.58549},"c17_Y_B1_2/Y":{"f":0.932688,"r":0.58549},"c17_Y_B2_0/Y":{"f":0.893139,"r":0.580777},"c17_Y_B2_1/Y":{"f":0.893139,"r":0.580777},"c17_Y_B2_2/Y":{"f":0.893139,"r":0.580777},"c17_u1/Y":{"f":0.269856,"r":0.657004},"c18_Y_A1_0/Y":{"f":2.582909,"r":1.195469},"c18_Y_A1_1/Y":{"f":2.582909,"r":1.195469},"c18_Y_A1_2/Y":{"f":2.582909,"r":1.195469},"c18_Y_A2_0/Y":{"f":2.601059,"r":1.22294},"c18_Y_A2_1/Y":{"f":2.601059,"r":1.22294},"c18_Y_A2_2/Y":{"f":2.601059,"r":1.22294},"c18_Y_B1_0/Y":{"f":2.431392,"r":1.204869},"c18_Y_B1_1/Y":{"f":2.431392,"r":1.204869},"c18_Y_B1_2/Y":{"f":2.431392,"r":1.204869},"c18_Y_C1_0/Y":{"f":2.411249,"r":1.184405},"c18_Y_C1_1/Y":{"f":2.411249,"r":1.184405},"c18_Y_C1_2/Y":{"f":2.411249,"r":1.184405},"c18_Y_D1_0/Y":{"f":2.409861,"r":1.122991},"c18_Y_D1_1/Y":{"f":2.409861,"r":1.122991},"c18_Y_D1_2/Y":{"f":2.409861,"r":1.122991},"c18_u1/Y":{"f":0.381808,"r":2.001358},"c19_Y_A1_0/Y":{"f":1.129072,"r":0.967178},"c19_Y_A1_1/Y":{"f":1.129072,"r":0.967178},"c19_Y_A1_2/Y":{"f":1.129072,"r":0.967178},"c19_Y_A2_0/Y":{"f":1.084097,"r":0.98234},"c19_Y_A2_1/Y":{"f":1.084097,"r":0.98234},"c19_Y_A2_2/Y":{"f":1.084097,"r":0.98234},"c19_Y_B1_0/Y":{"f":1.132185,"r":0.870835},"c19_Y_B1_1/Y":{"f":1.132185,"r":0.870835},"c19_Y_B1_2/Y":{"f":1.132185,"r":0.870835},"c19_Y_C1_0/Y":{"f":1.153674,"r":0.850731},"c19_Y_C1_1/Y":{"f":1.153674,"r":0.850731},"c19_Y_C1_2/Y":{"f":1.153674,"r":0.850731},"c19_Y_D1_0/Y":{"f":1.157551,"r":0.811793},"c19_Y_D1_1/Y":{"f":1.157551,"r":0.811793},"c19_Y_D1_2/Y":{"f":1.157551,"r":0.811793},"c19_u1/Y":{"f":0.48518,"r":0.809997},"c1_COUT_A_0/COUT":{"f":1.016608,"r":0.745454},"c1_COUT_A_0/SUM":{"f":1.098499,"r":1.200857},"c1_COUT_A_1/COUT":{"f":1.016608,"r":0.745454},"c1_COUT_A_1/SUM":{"f":1.098499,"r":1.200857},"c1_COUT_A_2/COUT":{"f":1.016608,"r":0.745454},"c1_COUT_A_2/SUM":{"f":1.098499,"r":1.200857},"c1_COUT_B_0/COUT":{"f":0.993765,"r":0.740891},"c1_COUT_B_0/SUM":{"f":1.08117,"r":1.175807},"c1_COUT_B_1/COUT":{"f":0.993765,"r":0.740891},"c1_COUT_B_1/SUM":{"f":1.08117,"r":1.175807},"c1_COUT_B_2/COUT":{"f":0.993765,"r":0.740891},"c1_COUT_B_2/SUM":{"f":1.08117,"r":1.175807},"c1_COUT_CIN_0/COUT":{"f":0.975738,"r":0.749476},"c1_COUT_CIN_0/SUM":{"f":1.047449,"r":1.166631},"c1_COUT_CIN_1/COUT":{"f":0.975738,"r":0.749476},"c1_COUT_CIN_1/SUM":{"f":1.047449,"r":1.166631},"c1_COUT_CIN_2/COUT":{"f":0.975738,"r":0.749476},"c1_COUT_CIN_2/SUM":{"f":1.047449,"r":1.166631},"c1_SUM_A_0/COUT":{"f":1.110046,"r":1.121996},"c1_SUM_A_0/SUM":{"f":1.342408,"r":1.294281},"c1_SUM_A_1/COUT":{"f":1.110046,"r":1.121996},"c1_SUM_A_1/SUM":{"f":1.342408,"r":1.294281},"c1_SUM_A_2/COUT":{"f":1.110046,"r":1.121996},"c1_SUM_A_2/SUM":{"f":1.342408,"r":1.294281},"c1_SUM_B_0/COUT":{"f":1.087716,"r":1.117385},"c1_SUM_B_0/SUM":{"f":1.354637,"r":1.269742},"c1_SUM_B_1/COUT":{"f":1.087716,"r":1.117385},"c1_SUM_B_1/SUM":{"f":1.354637,"r":1.269742},"c1_SUM_B_2/COUT":{"f":1.087716,"r":1.117385},"c1_SUM_B_2/SUM":{"f":1.354637,"r":1.269742},"c1_SUM_CIN_0/COUT":{"f":1.069784,"r":1.126116},"c1_SUM_CIN_0/SUM":{"f":1.362423,"r":1.260633},"c1_SUM_CIN_1/COUT":{"f":1.069784,"r":1.126116},"c1_SUM_CIN_1/SUM":{"f":1.362423,"r":1.260633},"c1_SUM_CIN_2/COUT":{"f":1.069784,"r":1.126116},"c1_SUM_CIN_2/SUM":{"f":1.362423,"r":1.260633},"c1_u1/COUT":{"f":0.555435,"r":0.440591},"c1_u1/SUM":{"f":0.644475,"r":0.815655},"c20_Y_A1_0/Y":{"f":1.826163,"r":0.9146},"c20_Y_A1_1/Y":{"f":1.826163,"r":0.9146},"c20_Y_A1_2/Y":{"f":1.826163,"r":0.9146},"c20_Y_A2_0/Y":{"f":1.85032,"r":0.927073},"c20_Y_A2_1/Y":{"f":1.85032,"r":0.927073},"c20_Y_A2_2/Y":{"f":1.85032,"r":0.927073},"c20_Y_B1_0/Y":{"f":1.76553,"r":0.879757},"c20_Y_B1_1/Y":{"f":1.76553,"r":0.879757},"c20_Y_B1_2/Y":{"f":1.76553,"r":0.879757},"c20_Y_B2_0/Y":{"f":1.770269,"r":0.90341},"c20_Y_B2_1/Y":{"f":1.770269,"r":0.90341},"c20_Y_B2_2/Y":{"f":1.770269,"r":0.90341},"c20_Y_C1_0/Y":{"f":1.732957,"r":0.820583},"c20_Y_C1_1/Y":{"f":1.732957,"r":0.820583},"c20_Y_C1_2/Y":{"f":1.732957,"r":0.820583},"c20_Y_C2_0/Y":{"f":1.716357,"r":0.850159},"c20_Y_C2_1/Y":{"f":1.716357,"r":0.850159},"c20_Y_C2_2/Y":{"f":1.716357,"r":0.850159},"c20_u1/Y":{"f":0.33319,"r":1.407565},"c21_Y_A0_0/Y":{"f":0.95254,"r":0.626839},"c21_Y_A0_1/Y":{"f":0.95254,"r":0.626839},"c21_Y_A0_2/Y":{"f":0.95254,"r":0.626839},"c21_Y_A1_0/Y":{"f":0.96204,"r":0.64076},"c21_Y_A1_1/Y":{"f":0.96204,"r":0.64076},"c21_Y_A1_2/Y":{"f":0.96204,"r":0.64076},"c21_Y_S_0/Y":{"f":0.947939,"r":1.060647},"c21_Y_S_1/Y":{"f":0.947939,"r":1.060647},"c21_Y_S_2/Y":{"f":0.947939,"r":1.060647},"c21_u1/Y":{"f":0.303647,"r":0.69609},"c22_Y_A0_0/Y":{"f":0.808026,"r":0.55091},"c22_Y_A0_1/Y":{"f":0.808026,"r":0.55091},"c22_Y_A0_2/Y":{"f":0.808026,"r":0.55091},"c22_Y_A1_0/Y":{"f":0.817359,"r":0.547712},"c22_Y_A1_1/Y":{"f":0.817359,"r":0.547712},"c22_Y_A1_2/Y":{"f":0.817359,"r":0.547712},"c22_Y_S_0/Y":{"f":0.803109,"r":1.020824},"c22_Y_S_1/Y":{"f":0.803109,"r":1.020824},"c22_Y_S_2/Y":{"f":0.803109,"r":1.020824},"c22_u1/Y":{"f":0.31551,"r":0.659959},"c23_X_A0_0/X":{"f":0.821089,"r":0.597485},"c23_X_A0_1/X":{"f":0.821089,"r":0.597485},"c23_X_A0_2/X":{"f":0.821089,"r":0.597485},"c23_X_A1_0/X":{"f":0.830858,"r":0.600478},"c23_X_A1_1/X":{"f":0.830858,"r":0.600478},"c23_X_A1_2/X":{"f":0.830858,"r":0.600478},"c23_X_S_0/X":{"f":0.844726,"r":0.739636},"c23_X_S_1/X":{"f":0.844726,"r":0.739636},"c23_X_S_2/X":{"f":0.844726,"r":0.739636},"c23_u1/X":{"f":0.445824,"r":0.367492},"c24_X_A0_0/X":{"f":1.412036,"r":0.993481},"c24_X_A0_1/X":{"f":1.412036,"r":0.993481},"c24_X_A0_2/X":{"f":1.412036,"r":0.993481},"c24_X_A1_0/X":{"f":1.425562,"r":1.010797},"c24_X_A1_1/X":{"f":1.425562,"r":1.010797},"c24_X_A1_2/X":{"f":1.425562,"r":1.010797},"c24_X_A2_0/X":{"f":1.41325,"r":1.005479},"c24_X_A2_1/X":{"f":1.41325,"r":1.005479},"c24_X_A2_2/X":{"f":1.41325,"r":1.005479},"c24_X_A3_0/X":{"f":1.398364,"r":1.000801},"c24_X_A3_1/X":{"f":1.398364,"r":1.000801},"c24_X_A3_2/X":{"f":1.398364,"r":1.000801},"c24_X_S0_0/X":{"f":1.378108,"r":1.261965},"c24_X_S0_1/X":{"f":1.378108,"r":1.261965},"c24_X_S0_2/X":{"f":1.378108,"r":1.261965},"c24_X_S1_0/X":{"f":1.153772,"r":1.138744},"c24_X_S1_1/X":{"f":1.153772,"r":1.138744},"c24_X_S1_2/X":{"f":1.153772,"r":1.138744},"c24_u1/X":{"f":0.780839,"r":0.629056},"c25_Y_A_0/Y":{"f":0.580596,"r":0.659492},"c25_Y_A_1/Y":{"f":0.580596,"r":0.659492},"c25_Y_A_2/Y":{"f":0.580596,"r":0.659492},"c25_Y_B_0/Y":{"f":0.583169,"r":0.688867},"c25_Y_B_1/Y":{"f":0.583169,"r":0.688867},"c25_Y_B_2/Y":{"f":0.583169,"r":0.688867},"c25_Y_C_0/Y":{"f":0.575216,"r":0.698825},"c25_Y_C_1/Y":{"f":0.575216,"r":0.698825},"c25_Y_C_2/Y":{"f":0.575216,"r":0.698825},"c25_Y_D_0/Y":{"f":0.571401,"r":0.685851},"c25_Y_D_1/Y":{"f":0.571401,"r":0.685851},"c25_Y_D_2/Y":{"f":0.571401,"r":0.685851},"c25_u1/Y":{"f":0.381674,"r":0.350184},"c26_Y_A_0/Y":{"f":0.479293,"r":0.600091},"c26_Y_A_1/Y":{"f":0.479293,"r":0.600091},"c26_Y_A_2/Y":{"f":0.479293,"r":0.600091},"c26_Y_B_0/Y":{"f":0.494648,"r":0.641763},"c26_Y_B_1/Y":{"f":0.494648,"r":0.641763},"c26_Y_B_2/Y":{"f":0.494648,"r":0.641763},"c26_Y_C_0/Y":{"f":0.49014,"r":0.661298},"c26_Y_C_1/Y":{"f":0.49014,"r":0.661298},"c26_Y_C_2/Y":{"f":0.49014,"r":0.661298},"c26_Y_D_0/Y":{"f":0.485577,"r":0.660299},"c26_Y_D_1/Y":{"f":0.485577,"r":0.660299},"c26_Y_D_2/Y":{"f":0.485577,"r":0.660299},"c26_u1/Y":{"f":0.391828,"r":0.336047},"c27_Y_A_0/Y":{"f":1.575143,"r":0.670752},"c27_Y_A_1/Y":{"f":1.575143,"r":0.670752},"c27_Y_A_2/Y":{"f":1.575143,"r":0.670752},"c27_Y_B_0/Y":{"f":1.537312,"r":0.659403},"c27_Y_B_1/Y":{"f":1.537312,"r":0.659403},"c27_Y_B_2/Y":{"f":1.537312,"r":0.659403},"c27_Y_C_0/Y":{"f":1.514548,"r":0.62958},"c27_Y_C_1/Y":{"f":1.514548,"r":0.62958},"c27_Y_C_2/Y":{"f":1.514548,"r":0.62958},"c27_Y_D_0/Y":{"f":1.511824,"r":0.570357},"c27_Y_D_1/Y":{"f":1.511824,"r":0.570357},"c27_Y_D_2/Y":{"f":1.511824,"r":0.570357},"c27_u1/Y":{"f":0.163825,"r":1.297722},"c28_Y_A_0/Y":{"f":1.41746,"r":0.495746},"c28_Y_A_1/Y":{"f":1.41746,"r":0.495746},"c28_Y_A_2/Y":{"f":1.41746,"r":0.495746},"c28_Y_B_0/Y":{"f":1.393356,"r":0.476017},"c28_Y_B_1/Y":{"f":1.393356,"r":0.476017},"c28_Y_B_2/Y":{"f":1.393356,"r":0.476017},"c28_Y_C_0/Y":{"f":1.362722,"r":0.434858},"c28_Y_C_1/Y":{"f":1.362722,"r":0.434858},"c28_Y_C_2/Y":{"f":1.362722,"r":0.434858},"c28_Y_D_0/Y":{"f":1.321399,"r":0.360648},"c28_Y_D_1/Y":{"f":1.321399,"r":0.360648},"c28_Y_D_2/Y":{"f":1.321399,"r":0.360648},"c28_u1/Y":{"f":0.139491,"r":1.283666},"c29_X_A_N_0/X":{"f":0.701384,"r":0.644456},"c29_X_A_N_1/X":{"f":0.701384,"r":0.644456},"c29_X_A_N_2/X":{"f":0.701384,"r":0.644456},"c29_X_B_N_0/X":{"f":0.731031,"r":0.660918},"c29_X_B_N_1/X":{"f":0.731031,"r":0.660918},"c29_X_B_N_2/X":{"f":0.731031,"r":0.660918},"c29_X_C_0/X":{"f":0.568867,"r":0.732687},"c29_X_C_1/X":{"f":0.568867,"r":0.732687},"c29_X_C_2/X":{"f":0.568867,"r":0.732687},"c29_X_D_0/X":{"f":0.581817,"r":0.73274},"c29_X_D_1/X":{"f":0.581817,"r":0.73274},"c29_X_D_2/X":{"f":0.581817,"r":0.73274},"c29_u1/X":{"f":0.304148,"r":0.442806},"c2_COUT_A_0/COUT":{"f":0.574585,"r":0.554971},"c2_COUT_A_0/SUM":{"f":0.669481,"r":0.662627},"c2_COUT_A_1/COUT":{"f":0.574585,"r":0.554971},"c2_COUT_A_1/SUM":{"f":0.669481,"r":0.662627},"c2_COUT_A_2/COUT":{"f":0.574585,"r":0.554971},"c2_COUT_A_2/SUM":{"f":0.669481,"r":0.662627},"c2_COUT_B_0/COUT":{"f":0.557523,"r":0.561342},"c2_COUT_B_0/SUM":{"f":0.652135,"r":0.658877},"c2_COUT_B_1/COUT":{"f":0.557523,"r":0.561342},"c2_COUT_B_1/SUM":{"f":0.652135,"r":0.658877},"c2_COUT_B_2/COUT":{"f":0.557523,"r":0.561342},"c2_COUT_B_2/SUM":{"f":0.652135,"r":0.658877},"c2_SUM_A_0/COUT":{"f":0.685118,"r":0.664514},"c2_SUM_A_0/SUM":{"f":0.779154,"r":0.773139},"c2_SUM_A_1/COUT":{"f":0.685118,"r":0.664514},"c2_SUM_A_1/SUM":{"f":0.779154,"r":0.773139},"c2_SUM_A_2/COUT":{"f":0.685118,"r":0.664514},"c2_SUM_A_2/SUM":{"f":0.779154,"r":0.773139},"c2_SUM_B_0/COUT":{"f":0.668142,"r":0.669627},"c2_SUM_B_0/SUM":{"f":0.762282,"r":0.769431},"c2_SUM_B_1/COUT":{"f":0.668142,"r":0.669627},"c2_SUM_B_1/SUM":{"f":0.762282,"r":0.769431},"c2_SUM_B_2/COUT":{"f":0.668142,"r":0.669627},"c2_SUM_B_2/SUM":{"f":0.762282,"r":0.769431},"c2_u1/COUT":{"f":0.300036,"r":0.307115},"c2_u1/SUM":{"f":0.405587,"r":0.424323},"c30_Y_A_0/Y":{"f":0.228003,"r":0.188852},"c30_Y_A_1/Y":{"f":0.228003,"r":0.188852},"c30_Y_A_2/Y":{"f":0.228003,"r":0.188852},"c30_u1/Y":{"f":0.083987,"r":0.132546},"c31_Y_A_0/Y":{"f":0.145644,"r":0.10477},"c31_Y_A_1/Y":{"f":0.145644,"r":0.10477},"c31_Y_A_2/Y":{"f":0.145644,"r":0.10477},"c31_u1/Y":{"f":0.057889,"r":0.112528},"c32_X_A_0/X":{"f":0.291983,"r":0.363227},"c32_X_A_1/X":{"f":0.291983,"r":0.363227},"c32_X_A_2/X":{"f":0.291983,"r":0.363227},"c32_u1/X":{"f":0.148047,"r":0.192092},"c33_X_A_0/X":{"f":0.269146,"r":0.230156},"c33_X_A_1/X":{"f":0.269146,"r":0.230156},"c33_X_A_2/X":{"f":0.269146,"r":0.230156},"c33_u1/X":{"f":0.146581,"r":0.128072},"c34_Y_A_0/Y":{"f":0.333774,"r":0.309377},"c34_Y_A_1/Y":{"f":0.333774,"r":0.309377},"c34_Y_A_2/Y":{"f":0.333774,"r":0.309377},"c34_Y_B_0/Y":{"f":0.332467,"r":0.317299},"c34_Y_B_1/Y":{"f":0.332467,"r":0.317299},"c34_Y_B_2/Y":{"f":0.332467,"r":0.317299},"c34_u1/Y":{"f":0.155353,"r":0.195797},"c35_Y_A_0/Y":{"f":0.524239,"r":0.318361},"c35_Y_A_1/Y":{"f":0.524239,"r":0.318361},"c35_Y_A_2/Y":{"f":0.524239,"r":0.318361},"c35_Y_B_0/Y":{"f":0.511326,"r":0.304131},"c35_Y_B_1/Y":{"f":0.511326,"r":0.304131},"c35_Y_B_2/Y":{"f":0.511326,"r":0.304131},"c35_u1/Y":{"f":0.109218,"r":0.369196},"c36_X_A_0/X":{"f":0.405848,"r":0.429568},"c36_X_A_1/X":{"f":0.405848,"r":0.429568},"c36_X_A_2/X":{"f":0.405848,"r":0.429568},"c36_X_B_0/X":{"f":0.425248,"r":0.428525},"c36_X_B_1/X":{"f":0.425248,"r":0.428525},"c36_X_B_2/X":{"f":0.425248,"r":0.428525},"c36_u1/X":{"f":0.216574,"r":0.225913},"c37_X_A_0/X":{"f":0.587563,"r":0.373418},"c37_X_A_1/X":{"f":0.587563,"r":0.373418},"c37_X_A_2/X":{"f":0.587563,"r":0.373418},"c37_X_B_0/X":{"f":0.570088,"r":0.370099},"c37_X_B_1/X":{"f":0.570088,"r":0.370099},"c37_X_B_2/X":{"f":0.570088,"r":0.370099},"c37_u1/X":{"f":0.299152,"r":0.196491},"c38_X_A_0/X":{"f":0.826464,"r":0.900898},"c38_X_A_1/X":{"f":0.826464,"r":0.900898},"c38_X_A_2/X":{"f":0.826464,"r":0.900898},"c38_X_B_0/X":{"f":0.827669,"r":0.894834},"c38_X_B_1/X":{"f":0.827669,"r":0.894834},"c38_X_B_2/X":{"f":0.827669,"r":0.894834},"c38_u1/X":{"f":0.271957,"r":0.606414},"c39_Y_A_0/Y":{"f":0.91294,"r":0.917515},"c39_Y_A_1/Y":{"f":0.91294,"r":0.917515},"c39_Y_A_2/Y":{"f":0.91294,"r":0.917515},"c39_Y_B_0/Y":{"f":0.898153,"r":0.919734},"c39_Y_B_1/Y":{"f":0.898153,"r":0.919734},"c39_Y_B_2/Y":{"f":0.898153,"r":0.919734},"c39_u1/Y":{"f":0.301974,"r":0.670734},"c3_X_A_0/X":{"f":0.952983,"r":0.656396},"c3_X_A_1/X":{"f":0.952983,"r":0.656396},"c3_X_A_2/X":{"f":0.952983,"r":0.656396},"c3_X_B_0/X":{"f":0.935707,"r":0.657253},"c3_X_B_1/X":{"f":0.935707,"r":0.657253},"c3_X_B_2/X":{"f":0.935707,"r":0.657253},"c3_X_C_0/X":{"f":0.953224,"r":0.676918},"c3_X_C_1/X":{"f":0.953224,"r":0.676918},"c3_X_C_2/X":{"f":0.953224,"r":0.676918},"c3_u1/X":{"f":0.502582,"r":0.380558},"c40_Y_A_0/Y":{"f":0.515004,"r":0.416466},"c40_Y_A_1/Y":{"f":0.515004,"r":0.416466},"c40_Y_A_2/Y":{"f":0.515004,"r":0.416466},"c40_Y_B_N_0/Y":{"f":0.38141,"r":0.645467},"c40_Y_B_N_1/Y":{"f":0.38141,"r":0.645467},"c40_Y_B_N_2/Y":{"f":0.38141,"r":0.645467},"c40_u1/Y":{"f":0.197113,"r":0.368241},"c41_Y_A_N_0/Y":{"f":0.467328,"r":0.418218},"c41_Y_A_N_1/Y":{"f":0.467328,"r":0.418218},"c41_Y_A_N_2/Y":{"f":0.467328,"r":0.418218},"c41_Y_B_0/Y":{"f":0.366124,"r":0.402648},"c41_Y_B_1/Y":{"f":0.366124,"r":0.402648},"c41_Y_B_2/Y":{"f":0.366124,"r":0.402648},"c41_u1/Y":{"f":0.237279,"r":0.228175},"c42_X_A_0/X":{"f":0.291772,"r":0.362279},"c42_X_A_1/X":{"f":0.291772,"r":0.362279},"c42_X_A_2/X":{"f":0.291772,"r":0.362279},"c42_u1/X":{"f":0.147925,"r":0.191369},"c43_Y_A_0/Y":{"f":0.17542,"r":0.180097},"c43_Y_A_1/Y":{"f":0.17542,"r":0.180097},"c43_Y_A_2/Y":{"f":0.17542,"r":0.180097},"c43_u1/Y":{"f":0.102031,"r":0.097781},"c44_X_A_0/X":{"f":0.552482,"r":0.537553},"c44_X_A_1/X":{"f":0.552482,"r":0.537553},"c44_X_A_2/X":{"f":0.552482,"r":0.537553},"c44_u1/X":{"f":0.277391,"r":0.272584},"c45_Y_A_0/Y":{"f":0.249149,"r":0.229128},"c45_Y_A_1/Y":{"f":0.249149,"r":0.229128},"c45_Y_A_2/Y":{"f":0.249149,"r":0.229128},"c45_Y_B_0/Y":{"f":0.252085,"r":0.246112},"c45_Y_B_1/Y":{"f":0.252085,"r":0.246112},"c45_Y_B_2/Y":{"f":0.252085,"r":0.246112},"c45_u1/Y":{"f":0.136337,"r":0.185463},"c4_X_A_0/X":{"f":0.800861,"r":0.496852},"c4_X_A_1/X":{"f":0.800861,"r":0.496852},"c4_X_A_2/X":{"f":0.800861,"r":0.496852},"c4_X_B_0/X":{"f":0.781075,"r":0.492706},"c4_X_B_1/X":{"f":0.781075,"r":0.492706},"c4_X_B_2/X":{"f":0.781075,"r":0.492706},"c4_X_C_0/X":{"f":0.791177,"r":0.506519},"c4_X_C_1/X":{"f":0.791177,"r":0.506519},"c4_X_C_2/X":{"f":0.791177,"r":0.506519},"c4_u1/X":{"f":0.422064,"r":0.280147},"c5_X_A_0/X":{"f":1.219337,"r":1.108038},"c5_X_A_1/X":{"f":1.219337,"r":1.108038},"c5_X_A_2/X":{"f":1.219337,"r":1.108038},"c5_X_B_0/X":{"f":1.123082,"r":1.033124},"c5_X_B_1/X":{"f":1.123082,"r":1.033124},"c5_X_B_2/X":{"f":1.123082,"r":1.033124},"c5_X_C_0/X":{"f":1.01373,"r":0.954538},"c5_X_C_1/X":{"f":1.01373,"r":0.954538},"c5_X_C_2/X":{"f":1.01373,"r":0.954538},"c5_u1/X":{"f":0.592084,"r":0.671414},"c6_X_A_0/X":{"f":1.094992,"r":1.088055},"c6_X_A_1/X":{"f":1.094992,"r":1.088055},"c6_X_A_2/X":{"f":1.094992,"r":1.088055},"c6_X_B_0/X":{"f":1.086955,"r":0.986474},"c6_X_B_1/X":{"f":1.086955,"r":0.986474},"c6_X_B_2/X":{"f":1.086955,"r":0.986474},"c6_X_C_0/X":{"f":0.950854,"r":0.88756},"c6_X_C_1/X":{"f":0.950854,"r":0.88756},"c6_X_C_2/X":{"f":0.950854,"r":0.88756},"c6_u1/X":{"f":0.587894,"r":0.551857},"c7_X_A_0/X":{"f":1.184697,"r":1.078008},"c7_X_A_1/X":{"f":1.184697,"r":1.078008},"c7_X_A_2/X":{"f":1.184697,"r":1.078008},"c7_X_B_0/X":{"f":1.100867,"r":1.006045},"c7_X_B_1/X":{"f":1.100867,"r":1.006045},"c7_X_B_2/X":{"f":1.100867,"r":1.006045},"c7_X_C_0/X":{"f":0.98666,"r":0.916507},"c7_X_C_1/X":{"f":0.98666,"r":0.916507},"c7_X_C_2/X":{"f":0.98666,"r":0.916507},"c7_u1/X":{"f":0.573734,"r":0.655988},"c8_Y_A1_0/Y":{"f":0.771905,"r":0.488734},"c8_Y_A1_1/Y":{"f":0.771905,"r":0.488734},"c8_Y_A1_2/Y":{"f":0.771905,"r":0.488734},"c8_Y_A2_0/Y":{"f":0.777156,"r":0.504893},"c8_Y_A2_1/Y":{"f":0.777156,"r":0.504893},"c8_Y_A2_2/Y":{"f":0.777156,"r":0.504893},"c8_Y_B1_0/Y":{"f":0.71619,"r":0.481859},"c8_Y_B1_1/Y":{"f":0.71619,"r":0.481859},"c8_Y_B1_2/Y":{"f":0.71619,"r":0.481859},"c8_u1/Y":{"f":0.199772,"r":0.548774},"c9_Y_A1_0/Y":{"f":0.677635,"r":0.38114},"c9_Y_A1_1/Y":{"f":0.677635,"r":0.38114},"c9_Y_A1_2/Y":{"f":0.677635,"r":0.38114},"c9_Y_A2_0/Y":{"f":0.686139,"r":0.393781},"c9_Y_A2_1/Y":{"f":0.686139,"r":0.393781},"c9_Y_A2_2/Y":{"f":0.686139,"r":0.393781},"c9_Y_B1_0/Y":{"f":0.625386,"r":0.365052},"c9_Y_B1_1/Y":{"f":0.625386,"r":0.365052},"c9_Y_B1_2/Y":{"f":0.625386,"r":0.365052},"c9_u1/Y":{"f":0.163246,"r":0.527963}}},"driver":{"T":0.095204,"pins":{"g2/Y":{"f":0.078866,"r":0.095204}},"po":{"y":{"f":0.078866,"r":0.095203}}},"driver_x":{"T":0.168016,"pins":{"g2/Y":{"f":0.13759,"r":0.168017}},"po":{"y":{"f":0.13759,"r":0.168016}}},"fa_ripple":{"T":6.278229,"po":{"cout":{"f":6.161509,"r":2.798309},"s0":{"f":0.522003,"r":0.582843},"s1":{"f":0.913893,"r":0.962184},"s10":{"f":4.331351,"r":4.379642},"s11":{"f":4.711069,"r":4.759359},"s12":{"f":5.090786,"r":5.139077},"s13":{"f":5.470504,"r":5.518794},"s14":{"f":5.850222,"r":5.898512},"s15":{"f":6.229939,"r":6.278229},"s2":{"f":1.293611,"r":1.341902},"s3":{"f":1.673328,"r":1.721619},"s4":{"f":2.053046,"r":2.101337},"s5":{"f":2.432763,"r":2.481053},"s6":{"f":2.812481,"r":2.860771},"s7":{"f":3.192198,"r":3.240489},"s8":{"f":3.571916,"r":3.620206},"s9":{"f":3.951633,"r":3.999924}}},"fa_ripple_x":{"T":6.384998,"po":{"cout":{"f":6.268277,"r":2.926336},"s0":{"f":0.628717,"r":0.689578},"s1":{"f":1.020642,"r":1.068933},"s10":{"f":4.438112,"r":4.486403},"s11":{"f":4.817832,"r":4.866123},"s12":{"f":5.19755,"r":5.245842},"s13":{"f":5.577269,"r":5.62556},"s14":{"f":5.956988,"r":6.005279},"s15":{"f":6.336707,"r":6.384998},"s2":{"f":1.40036,"r":1.448651},"s3":{"f":1.78008,"r":1.828371},"s4":{"f":2.159799,"r":2.20809},"s5":{"f":2.539518,"r":2.587809},"s6":{"f":2.919237,"r":2.967528},"s7":{"f":3.298955,"r":3.347247},"s8":{"f":3.678675,"r":3.726966},"s9":{"f":4.058393,"r":4.106685}}},"gates2":{"T":2.0511,"po":{"cout":{"f":2.0511,"r":1.493766},"s0":{"f":0.44683,"r":0.41459},"s1":{"f":0.476876,"r":0.615753},"s2":{"f":0.85424,"r":0.859703},"s3":{"f":0.940698,"r":0.996043},"s4":{"f":1.324911,"r":1.330373},"s5":{"f":1.411367,"r":1.466714},"s6":{"f":1.795581,"r":1.801044},"s7":{"f":1.882038,"r":1.937385},"z0":{"f":0.347465,"r":0.476344},"z2":{"f":0.631581,"r":0.845123},"z4":{"f":0.945435,"r":1.315793},"z6":{"f":1.259288,"r":1.786463}}},"gates2_x":{"T":2.158512,"po":{"cout":{"f":2.158512,"r":1.611097},"s0":{"f":0.564161,"r":0.53192},"s1":{"f":0.594207,"r":0.733086},"s2":{"f":0.961652,"r":0.967114},"s3":{"f":1.04811,"r":1.103455},"s4":{"f":1.432322,"r":1.437784},"s5":{"f":1.51878,"r":1.574125},"s6":{"f":1.902992,"r":1.908455},"s7":{"f":1.98945,"r":2.044796},"z0":{"f":0.454701,"r":0.593675},"z2":{"f":0.748914,"r":0.952535},"z4":{"f":1.062767,"r":1.423204},"z6":{"f":1.376619,"r":1.893875}}},"maj_xor3":{"T":6.153885,"po":{"cout":{"f":6.153885,"r":3.134975},"s0":{"f":0.441471,"r":0.424412},"s1":{"f":0.611728,"r":0.632082},"s10":{"f":4.066266,"r":4.08662},"s11":{"f":4.450103,"r":4.470457},"s12":{"f":4.833941,"r":4.854295},"s13":{"f":5.217778,"r":5.238132},"s14":{"f":5.601615,"r":5.62197},"s15":{"f":5.985453,"r":6.005807},"s2":{"f":0.995565,"r":1.015919},"s3":{"f":1.379402,"r":1.399756},"s4":{"f":1.76324,"r":1.783594},"s5":{"f":2.147078,"r":2.167431},"s6":{"f":2.530915,"r":2.551269},"s7":{"f":2.914753,"r":2.935107},"s8":{"f":3.298591,"r":3.318944},"s9":{"f":3.682428,"r":3.702783}}},"maj_xor3_x":{"T":6.25944,"po":{"cout":{"f":6.25944,"r":3.268525},"s0":{"f":0.554201,"r":0.519894},"s1":{"f":0.717236,"r":0.73759},"s10":{"f":4.171803,"r":4.192159},"s11":{"f":4.555645,"r":4.575999},"s12":{"f":4.939486,"r":4.95984},"s13":{"f":5.323327,"r":5.343681},"s14":{"f":5.707168,"r":5.727522},"s15":{"f":6.091008,"r":6.111363},"s2":{"f":1.101076,"r":1.121431},"s3":{"f":1.484918,"r":1.505272},"s4":{"f":1.868758,"r":1.889113},"s5":{"f":2.252599,"r":2.272954},"s6":{"f":2.63644,"r":2.656795},"s7":{"f":3.020281,"r":3.040636},"s8":{"f":3.404122,"r":3.424477},"s9":{"f":3.787963,"r":3.808318}}},"mux2i_tree":{"T":0.672324,"po":{"y":{"f":0.550323,"r":0.672324}}},"mux2i_tree_x":{"T":1.454669,"po":{"y":{"f":1.302197,"r":1.454669}}},"nand4_tree":{"T":0.680156,"po":{"y":{"f":0.680156,"r":0.260177}}},"nand4_tree_x":{"T":0.757072,"po":{"y":{"f":0.757072,"r":0.335997}}}}'''


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--emit":
        _emit(sys.argv[2])
    elif len(sys.argv) == 3 and sys.argv[1] == "--record":
        _record(sys.argv[2])
    else:
        unittest.main(verbosity=2)
