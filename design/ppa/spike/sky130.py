"""sky130_fd_sc_hd glue for the PPA spike (WP-X1): reuses WP-X0's liberty.py / netlist.py / engine.py
unchanged and adds only what the second library needs.

  * 1-D liberty tables (sky130's input-pin internal_power tables have no index_2) -- `liberty.Table`
    is replaced by a subclass that accepts them. Everything else in liberty.py is untouched.
  * units: this liberty is ns / pF (NOT fF) / V / nW / mA, so internal_power is V*mA*ns = pJ.
  * the fixed timing setup of the study (PI transition, PO load) and VDD = 1.8 V.
  * the CELL POLICY: `cell_class(name)` puts every one of the 428 cell groups in a class; only class
    "logic" may appear in a scored netlist of a combinational task.
  * `expand_generic_sky`: the scored `abc -g` gate netlist re-expressed as sky130 cells (flow A0').
  * `energy_fj`: switching + internal energy in fJ with the right units (flow-independent).
"""
import re

import engine as E
import fetch_sky130
import liberty as L
import netlist as N

PREFIX = "sky130_fd_sc_hd__"
NAND2_UM2 = 3.7536          # sky130_fd_sc_hd__nand2_1
VDD = 1.8                   # V, tt_025C_1v80
# The fixed timing setup (see sky130.md section 3): every primary input is driven by an ideal ramp of
# PI_SLEW_NS, every primary output bit carries PO_LOAD_PF (about 4.3 x the input capacitance of inv_1),
# arrival at the inputs 0, no wire capacitance, no required time (T = latest output arrival).
PI_SLEW_NS = 0.05
PO_LOAD_PF = 0.010


# ---------------------------------------------------------------- 1-D table support
class _Table(L.Table):
    """liberty.Table that also accepts 1-D tables (index_1 only: sky130's input-pin power tables) and scalar tables
    (`rise_power ("scalar") { values("0.0") }`: the zero-power arcs of its reset flops)."""
    __slots__ = ()

    def __init__(self, g):
        if "index_2" in g.attrs:
            super().__init__(g)
            return
        vals = g.attrs["values"]
        row = [float(x) for x in (vals[0] if isinstance(vals, list) else vals).split(",")]
        if "index_1" in g.attrs:
            self.i1 = [float(x) for x in g.attrs["index_1"][0].split(",")]
        else:
            self.i1 = [0.0, 1.0]
            row = [row[0], row[0]]
        self.i2 = [0.0, 1.0]
        self.v = [[x, x] for x in row]


L.Table = _Table


_compile_function = L.compile_function


def _compile_function_const(expr):
    """liberty.compile_function plus the constants "0" / "1" (tie cell conb_1: HI = 1, LO = 0)."""
    e = expr.strip()
    if e in ("0", "1"):
        return "M" if e == "1" else "0"
    return _compile_function(expr)


L.compile_function = _compile_function_const


def load_lib():
    return L.Liberty.load(fetch_sky130.lib_path())


# ---------------------------------------------------------------- the cell policy
# First match wins. "logic" = allowed in a scored netlist of a combinational task, at every drive strength.
POLICY = [
    (r"^lpflow_",                       "low-power-flow",  "isolation, level shifter, bleeder, power-gated clock/decap cells need extra supply rails"),
    (r"^(fill|decap|tap|diode|probe|probec_p|macro_sparecell)", "physical-only", "filler, decap, tap, antenna diode, probe point, spare cell: no logic function"),
    (r"^(df|sdf|edf|sedf)",             "sequential",      "flip-flops (plain, reset/set, scan, enable): combinational tasks have none"),
    (r"^(dl[rx]|sdlclkp|dlclkp)",       "sequential",      "latches and clock gates"),
    (r"^dly",                           "delay",           "delay cells (dlygate*, dlymetal*): a buffer chosen for its delay; ABC would use them to equalize paths"),
    (r"^clk",                           "clock",           "clock buffers/inverters/delay buffers (clkbuf, clkinv, clkinvlp, clkdlybuf*): clock-tree cells"),
    (r"^(ebufn|einvn|einvp)",           "tristate",        "tri-state: a third output state (z) the 2-state netlist simulation cannot see"),
    (r"^(fa|fah|fahcin|fahcon|ha)_",    "multi-output",    "adder cells with two outputs: ABC's mapper handles single-output cells only; extract_fa is not in the flow"),
    (r"^conb_",                         "tie",             "tie cell: inserted by the flow's hilomap step, never chosen by the mapper"),
]


def cell_class(name):
    """(class, reason) of a cell name (with or without the library prefix)."""
    n = name[len(PREFIX):] if name.startswith(PREFIX) else name
    for pat, cls, why in POLICY:
        if re.search(pat, n):
            return cls, why
    return "logic", "ordinary combinational cell"


# Yosys `abc -dont_use` patterns (ABC `read_lib -X`, glob syntax) equivalent to POLICY minus the "logic" class.
DONT_USE = [PREFIX + p for p in [
    "lpflow_*", "fill_*", "decap_*", "tap*", "diode_*", "probe*", "macro_sparecell*",
    "df*", "sdf*", "edf*", "sedf*", "dlr*", "dlx*", "dlclkp_*", "sdlclkp_*",
    "dly*", "clk*", "ebufn_*", "einvn_*", "einvp_*", "fa_*", "fah*", "ha_*", "conb_*"]]


def dont_use_args():
    return " ".join(f"-dont_use {p}" for p in DONT_USE)


# ---------------------------------------------------------------- A0': the scored gates as sky130 cells
GENERIC_TO_SKY = {
    # kind: (cell, {generic pin: cell pin}, generic Y -> cell output pin)
    "$_NOT_":  ("inv_1",   {"A": "A"},                   "Y"),
    "$_NAND_": ("nand2_1", {"A": "A", "B": "B"},         "Y"),
    "$_NOR_":  ("nor2_1",  {"A": "A", "B": "B"},         "Y"),
    "$_AND_":  ("and2_1",  {"A": "A", "B": "B"},         "X"),
    "$_OR_":   ("or2_1",   {"A": "A", "B": "B"},         "X"),
    "$_XOR_":  ("xor2_1",  {"A": "A", "B": "B"},         "X"),
    "$_XNOR_": ("xnor2_1", {"A": "A", "B": "B"},         "Y"),
    "$_MUX_":  ("mux2_1",  {"A": "A0", "B": "A1", "S": "S"}, "X"),
    # A & ~B = nor2b(A := B, B_N := A);  A | ~B = nand2b(A_N := A, B := B): one 6.256 um^2 cell each
    "$_ANDNOT_": ("nor2b_1",  {"A": "B_N", "B": "A"},    "Y"),
    "$_ORNOT_":  ("nand2b_1", {"A": "A_N", "B": "B"},    "Y"),
}
# sky130_fd_sc_hd__ordinary cost-model mapping of ANDNOT/ORNOT alternatives (for the table in sky130.md)
ANDNOT_ALT = {"$_ANDNOT_": [("nor2b_1", 6.256), ("and2b_1", 7.5072), ("inv_1+nor2_1", 7.5072)],
              "$_ORNOT_": [("nand2b_1", 6.256), ("or2b_1", 7.5072), ("inv_1+nand2_1", 7.5072)]}


def expand_generic_sky(nl):
    """The scored netlist (Yosys `$_X_` gates) as sky130_fd_sc_hd cell instances, one cell per gate."""
    out = N.Netlist()
    out.name, out.ports, out.alias, out.pi, out.po = nl.name, nl.ports, nl.alias, nl.pi, nl.po
    for g in nl.gates:
        if g.kind not in GENERIC_TO_SKY:
            raise ValueError(f"unsupported generic cell {g.kind}")
        cell, pm, zo = GENERIC_TO_SKY[g.kind]
        pins = {pm[p]: n for p, n in g.pins.items() if p in pm}
        pins[zo] = g.pins["Y"]
        out.gates.append(N.Gate(PREFIX + cell, g.inst, pins))
    return out


# ---------------------------------------------------------------- measurement helpers
def policy_report(nl, lib):
    """(cell histogram, violations) of a mapped netlist: every instance must be a library cell of class
    "logic"; anything else (a flop, a tie, a clock buffer, an unknown name) is a violation."""
    hist, bad = {}, {}
    for g in nl.gates:
        hist[g.kind] = hist.get(g.kind, 0) + 1
        if not lib.has(g.kind):
            bad[g.kind] = "not in the liberty"
            continue
        cls, why = cell_class(g.kind)
        if cls != "logic":
            bad[g.kind] = cls
    return dict(sorted(hist.items())), bad


def short(name):
    return name[len(PREFIX):] if name.startswith(PREFIX) else name


def timing(d, pi_slew=PI_SLEW_NS, po_load=PO_LOAD_PF):
    """(T_ns, critical path) of a Design under the fixed setup."""
    t, path, _ = d.sta_nldm(pi_slew, po_load)
    return t, path


def mean(xs):
    xs = list(xs)
    return sum(xs) / len(xs) if xs else 0.0


def switching_fj(d, rises, falls, po_load=PO_LOAD_PF):
    """sum over nets of toggles * 1/2 C V^2, C in pF -> fJ (x1000). Same definition as run_spike.switching_energy_fj
    with sky130's units; primary inputs count with their fan-out pin capacitance."""
    tot = 0.0
    for net in sorted(set(rises) | set(falls)):
        if net in ("0", "1"):
            continue
        c = d.load_cache.get(net)
        if c is None:
            c = d.load_ff(net, po_load)
        tot += (rises.get(net, 0) + falls.get(net, 0)) * 0.5 * c * VDD * VDD
    return tot * 1000.0


def internal_fj(d, rises, falls, pi_slew=PI_SLEW_NS):
    """liberty internal_power of the output pins: per rise the mean of the rise_power tables, per fall the mean of the
    fall_power tables, at (worst input slew, load). pJ -> fJ (x1000). The tables are SIGNED and already contain
    +-1/2 C V^2 of the load (rise positive, fall negative), so only the sum over a rise+fall pair is the cell's own
    energy: rises and falls alternate on every net, which makes r*er + f*ef correct (sky130.md section 2)."""
    tot = 0.0
    for i, c in enumerate(d.cells):
        for op, onet in d.outs[i].items():
            r, f = rises.get(onet, 0), falls.get(onet, 0)
            if not (r or f):
                continue
            slew = d.gate_delay[(i, op)][2] or pi_slew
            load = d.load_cache[onet]
            pw = c.power[op]
            if not pw["rise_power"] or not pw["fall_power"]:
                continue
            er = mean(t.at(slew, load) for t in pw["rise_power"])
            ef = mean(t.at(slew, load) for t in pw["fall_power"])
            tot += r * er + f * ef
    return tot * 1000.0
