#!/usr/bin/env python3.12
"""svGolf COMPOSED score: area and clock period of a design too large to flatten, module by module (ASAP7 view).

A large regular design (tasks of kind `explore-stream`: 16,384 multiply-accumulate cells at the scored size) cannot be
flattened by the pinned WebAssembly Yosys (4 GiB). This file measures every DISTINCT module once and composes:

  flow      stage 1 is canon.ys with one line changed (canon_hier.ys: every module keeps its hierarchy), stage 2 is the
            pinned clocked script svgolf_seq.ys without its `ltp` line (svgolf_seq_hier.ys): the same passes, run on
            every module. A block of the SRAM catalogue (score/sram_asap7.json) stays an instance.
  area      every module's OWN cells are weighed by the ASAP7 view (score/ppa.py, `asap7_a0_v1`: each gate one cell,
            repaired by buffering, flip-flops included) with its child instances cut at their pins; the design's area
            is sum(instances x own area) over the modules, plus sum(instances x table area) over the catalogue
            blocks.
  period    max over the modules of each module's own register-to-register period at the scored parameters (the view's
            period of the cut module: paths from its inputs and registers to its registers and outputs). `--flat`
            (a tool, not part of the score) gives the period of a WHOLE design flattened at a small point, to compare.
  rule      the composition is meaningful because of the HIERARCHY RULE, checked here on the netlist: in every
            module below the top each output is a register output, a child's output, or a module input passed
            through, and each input of a child instance is driven by a register, a child output, a module input or a
            constant (a catalogue block's inputs are exempt). No combinational path then crosses a module boundary
            inside logic.

What the composed score leaves out, by construction: wires, the clock tree, the delay of nets that fan out across module
boundaries (their buffers are counted as area in the module that drives them), and a catalogue block's own
clock-to-output and setup times (a block's port is timed as a module boundary). It is labelled `composed`, never ranked
against a flat score.

    python3.12 score/hier.py DESIGN.sv --top gemm --param LGE=7 --param LAT=32 [--json OUT] [--work DIR]
    python3.12 score/hier.py DESIGN.sv --top gemm --param LGE=2 --param LAT=3 --flat     # the flat check-point run
    python3.12 score/hier.py DESIGN.sv --top gemm --param LGE=2 --param LAT=3 --rules    # the hierarchy rule only

Exit status 0 weighed (and the rule holds), 1 refused (the rule, an illegal netlist, a failed synthesis), 2 usage.
"""
import argparse
import json
import os
import re
import shutil
import sys
import tempfile
import time
from decimal import Decimal

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ppa  # noqa: E402
import score  # noqa: E402

VERSION = "composed_asap7_v1"
CANON_HIER = os.path.join(HERE, "canon_hier.ys")
SEQ_HIER = os.path.join(HERE, "svgolf_seq_hier.ys")
SRAM_TABLE = os.path.join(HERE, "sram_asap7.json")
FLOP = "$_DFF_P_"
PDK = "asap7"


class HierError(Exception):
    """The design cannot be scored (its fault, or the flow's limit); the message says which."""


class RuleError(HierError):
    """The hierarchy rule does not hold; `.findings` lists where."""

    def __init__(self, findings):
        super().__init__("the hierarchy rule does not hold: " + "; ".join(findings[:6])
                         + (f" (and {len(findings) - 6} more)" if len(findings) > 6 else ""))
        self.findings = findings


def sram_table(path=SRAM_TABLE):
    with open(path) as fh:
        t = json.load(fh)
    return {b["name"]: b for b in t["blocks"]}, t


def sram_blackboxes(table):
    out = []
    for b in table.values():
        out.append(f"(* blackbox *)\nmodule {b['name']} (\n  input  logic clk,\n"
                   f"  input  logic [{b['addr_bits'] - 1}:0] ADDRESS,\n  input  logic [{b['width'] - 1}:0] wd,\n"
                   "  input  logic banksel, read, write,\n"
                   f"  output logic [{b['width'] - 1}:0] dataout\n);\nendmodule\n")
    return "\n".join(out)


SRAM_IN = ("clk", "ADDRESS", "wd", "banksel", "read", "write")
SRAM_OUT = ("dataout",)


# --------------------------------------------------------------------------------------------------- synthesis
def synthesize(sources, top, params, work, flat=False, yosys=None):
    """The two-stage flow with the SRAM black boxes: the netlist path and the run's facts. `flat`: canon.ys (the
    whole design flattened: a check-point run); else canon_hier.ys (every module kept)."""
    yosys = score.yosys_bin(yosys)
    table, _ = sram_table()
    os.makedirs(work, exist_ok=True)
    lib = os.path.join(work, "sram_blackbox.sv")
    with open(lib, "w") as fh:
        fh.write(sram_blackboxes(table))
    read, _ = score.gate_sources(list(sources), work)
    il, netlist = os.path.join(work, "canon.il"), os.path.join(work, "netlist.v")
    stat, ltp = os.path.join(work, "stat.json"), os.path.join(work, "ltp.txt")
    canon = score.CANON_SCRIPT if flat else CANON_HIER
    seq = score.FLOWS["seq"][0] if flat else SEQ_HIER
    t0 = time.time()
    try:
        score.run_yosys(yosys, score.render_canon(read + [lib], top, params, il, canon), work, "canon", read + [lib])
        if flat:
            text = score.render_script(il, top, stat, ltp, netlist, seq)
        else:
            text = score.fill_template(seq, {"@RTLIL@": f'"{il}"', "@TOP@": top, "@STAT@": f'"{stat}"',
                                             "@NETLIST@": f'"{netlist}"'})
        score.run_yosys(yosys, text, work, "synth")
    except score.ScoreError as e:
        said = str(e)
        if "bad_alloc" in said or "unreachable" in said:
            # the rating build's 4 GiB: one module is too large for it (or, flat, the whole design)
            where = ""
            log = os.path.join(work, "synth.log")
            if os.path.isfile(log):
                with open(log, errors="replace") as fh:
                    mods = re.findall(r"module (\\\S+|\$paramod\S+)", fh.read()[-4000:])
                where = f" (last seen: {show(mods[-1].lstrip(chr(92)))})" if mods else ""
            raise HierError("the pinned flow ran out of the rating build's memory (4 GiB)"
                            + (" flattening the design at this point" if flat else
                               f" on one module{where}: a module's own logic is synthesized whole, so split a large "
                               "module into smaller ones (and avoid run-time indexing of wide vectors)"))
        raise HierError(f"the pinned flow failed{'' if flat else ' with the hierarchy kept'}: {said[-1500:]}")
    with open(os.path.join(work, "synth.log"), errors="replace") as fh:
        removals = score.flop_removals(fh.read())
    bad = [ln for k in ("undefined", "constant_one_or_x", "memory_undefined", "fsm_mapped") for ln in removals.get(k) or []]
    if bad:
        raise HierError("never-loaded register or memory: the pinned flow removes a flip-flop while reads of it remain "
                        f"(its log: `{bad[0]}`" + (f" and {len(bad) - 1} more" if len(bad) > 1 else "") + "); reset it, "
                        "load it with a value other than its own, or remove it (the rule of every clocked task)")
    return netlist, {"yosys_version": score.yosys_version(yosys), "rating_build": score.is_rating_build(yosys),
                     "canon_script_sha256": score.sha256_file(canon), "script_sha256": score.sha256_file(seq),
                     "rtlil_sha256": score.sha256_file(il), "netlist_sha256": score.sha256_file(netlist),
                     "seconds": round(time.time() - t0, 1)}


# ------------------------------------------------------------------------------------------- reading the netlist
_MOD_RE = re.compile(r"^module\s+(\\\S+|[^\s(]+)\s*\(([^;]*)\);\n(.*?)^endmodule", re.M | re.S)
_DECL_RE = re.compile(r"^\s*(input|output|inout|wire)\s*(?:\[(\d+):(\d+)\])?\s*(\\\S+|[^\s;]+)\s*;", re.M)
_CELL_RE = re.compile(r"^\s*(\\\S+|[^\s(;=]+)\s+(\\\S+|[^\s(;=]+)\s*\(\s*((?:\.[\w$]+\s*\([^)]*\)\s*,?\s*)*)\)\s*;", re.M)
_PIN_RE = re.compile(r"\.([\w$]+)\s*\(([^)]*)\)")
_ASSIGN_RE = re.compile(r"^\s*assign\s+(.+?)\s*=\s*(.+?);", re.M | re.S)
_KEYWORDS = {"module", "input", "output", "inout", "wire", "reg", "assign", "endmodule"}


class Module:
    def __init__(self, name):
        self.name = name
        self.ports = []            # (name, direction, width), in declaration order
        self.widths = {}           # vector -> (hi, lo)
        self.gates = []            # (kind, instance, {pin: bit})
        self.children = []         # (type, instance, {pin: [bits, MSB first]})
        self.alias = {}            # bit -> bit
        self.gate_text = []        # the text of the gate instances and assigns, as Yosys wrote them
        self.decl_text = []

    def resolve(self, bit):
        n = 0
        while bit in self.alias:
            bit = self.alias[bit]
            n += 1
            if n > 1000000:
                raise HierError(f"netlist: alias loop in {self.name}")
        return bit


def read_netlist(text):
    """The modules of a hierarchical netlist `write_verilog -noattr -noexpr` wrote: {name: Module}."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    mods = {}
    for m in _MOD_RE.finditer(text):
        name, body = m.group(1).lstrip("\\"), m.group(3)
        mod = Module(name)
        for d in _DECL_RE.finditer(body):
            kind, hi, lo, n = d.groups()
            if kind == "inout":
                raise HierError(f"netlist: inout port {n} in {name}")
            if hi is not None:
                mod.widths.setdefault(n, (int(hi), int(lo)))
            if kind != "wire":
                mod.ports.append((n, kind, 1 if hi is None else int(hi) - int(lo) + 1))
        for a in _ASSIGN_RE.finditer(body):
            lhs, rhs = ppa._bits(a.group(1), mod.widths), ppa._bits(a.group(2), mod.widths, xok=True)
            if len(lhs) != len(rhs):
                raise HierError(f"netlist: assign width mismatch in {name}: {a.group(0)[:80]!r}")
            for l, r in zip(lhs, rhs):
                mod.alias[l] = r
            mod.gate_text.append(a.group(0))
        ncell = 0
        for c in _CELL_RE.finditer(body):
            kind, inst = c.group(1).lstrip("\\"), c.group(2)
            if kind in _KEYWORDS:
                continue
            ncell += 1
            pins = {p.group(1): ppa._bits(p.group(2), mod.widths) if p.group(2).strip() else []
                    for p in _PIN_RE.finditer(c.group(3))}
            if re.fullmatch(r"\$_\w+_", kind):
                bad = [p for p, b in pins.items() if len(b) != 1]
                if bad:
                    raise HierError(f"netlist: gate pin {bad[0]} of {kind} in {name} is not one bit")
                mod.gates.append((kind, inst, {p: b[0] for p, b in pins.items()}))
                mod.gate_text.append(c.group(0))
            else:
                mod.children.append((kind, inst, pins))
        opened = len(re.findall(r"^\s*(?!module\b|input\b|output\b|inout\b|wire\b|reg\b|assign\b)(?:\\\S+|[^\s(;=]+)"
                                r"\s+(?:\\\S+|[^\s(;=]+)\s*\(", body, re.M))
        if opened != ncell:
            raise HierError(f"netlist: some instances of {name} could not be read ({opened} opened, {ncell} read)")
        mods[name] = mod
    if not mods:
        raise HierError("netlist: no module found")
    return mods


def pin_dirs(mods, table, kind):
    """{pin: 'input' | 'output'} of a child type: a module of the netlist, or a catalogue block."""
    if kind in table:
        return {**dict.fromkeys(SRAM_IN, "input"), **dict.fromkeys(SRAM_OUT, "output")}
    if kind not in mods:
        raise HierError(f"netlist: instance of `{kind}`, which is neither a module of the design nor a block of the "
                        "SRAM catalogue (score/sram_asap7.json)")
    return {n: d for n, d, _ in mods[kind].ports}


def clock_ports(mods, table):
    """{module: set of input ports that are clocks}: an input every use of which is a flip-flop's clock pin or a
    child's clock port. Computed bottom-up (a module's children first)."""
    out, order = {}, topo_order(mods, table)
    for name in order:
        mod = mods[name]
        use = {}                                     # resolved bit -> True while every use is a clock use
        for kind, _, pins in mod.gates:
            for p, b in pins.items():
                if p in ("Y", "Q"):
                    continue
                r = mod.resolve(b)
                use[r] = use.get(r, True) and (kind == FLOP and p == "C")
        for kind, _, pins in mod.children:
            dirs = pin_dirs(mods, table, kind)
            cks = {"clk"} if kind in table else out[kind]
            for p, bits in pins.items():
                if dirs.get(p) != "input":
                    continue
                for b in bits:
                    r = mod.resolve(b)
                    use[r] = use.get(r, True) and (p in cks)
        outs = {mod.resolve(b) for n, d, _ in mod.ports if d == "output" for b in ppa._bits(n, mod.widths)}
        out[name] = {n for n, d, w in mod.ports
                     if d == "input" and w == 1 and use.get(n) is True and n not in outs}
    return out


def topo_order(mods, table):
    """The modules, children before parents."""
    seen, order = set(), []

    def visit(n, stack=()):
        if n in seen:
            return
        if n in stack:
            raise HierError(f"netlist: recursive instantiation of {n}")
        for kind, _, _ in mods[n].children:
            if kind in mods:
                visit(kind, stack + (n,))
            elif kind not in table:
                pin_dirs(mods, table, kind)          # raises: an unknown cell
        seen.add(n)
        order.append(n)
    for n in mods:
        visit(n)
    return order


def instance_counts(mods, table, top):
    """How many instances of every module and catalogue block the design has."""
    counts = {n: 0 for n in mods}
    blocks = {}
    counts[top] = 1
    for name in reversed(topo_order(mods, table)):   # parents before children
        if not counts[name]:
            continue
        for kind, _, _ in mods[name].children:
            if kind in table:
                blocks[kind] = blocks.get(kind, 0) + counts[name]
            else:
                counts[kind] += counts[name]
    return counts, blocks


def drivers(mod, mods, table, clocks):
    """{resolved bit: 'reg' | 'logic' | 'child' | 'input'} for every driven bit of `mod`."""
    drv = {}
    for kind, _, pins in mod.gates:
        out = pins.get("Q" if kind == FLOP else "Y")
        if out is not None:
            drv[out] = "reg" if kind == FLOP else "logic"
    for kind, _, pins in mod.children:
        dirs = pin_dirs(mods, table, kind)
        for p, bits in pins.items():
            if dirs.get(p) == "output":
                for b in bits:
                    drv[b] = "child"
    for n, d, _ in mod.ports:
        if d == "input":
            for b in ppa._bits(n, mod.widths):
                drv[b] = "input"
    return drv


def rule_findings(mods, table, top, clocks=None):
    """Where the hierarchy rule fails, in words ([]: it holds)."""
    clocks = clocks or clock_ports(mods, table)
    bad = []
    for name in sorted(mods):
        mod = mods[name]
        drv = drivers(mod, mods, table, clocks)
        if name != top:
            for n, d, _ in mod.ports:
                if d != "output":
                    continue
                hits = [b for b in ppa._bits(n, mod.widths) if drv.get(mod.resolve(b)) == "logic"]
                if hits:
                    bad.append(f"module {show(name)}: output `{n}` is driven by logic ({len(hits)} bit"
                               f"{'s' if len(hits) > 1 else ''}, e.g. {hits[0]}); an output of a module below the top is "
                               "a register output, a child's output or a module input")
        for kind, inst, pins in mod.children:
            if kind in table:
                continue                              # a catalogue block's inputs may be driven by logic
            dirs = pin_dirs(mods, table, kind)
            for p, bits in sorted(pins.items()):
                if dirs.get(p) != "input":
                    continue
                hits = [b for b in bits if drv.get(mod.resolve(b)) == "logic"]
                if hits:
                    bad.append(f"module {show(name)}: input `{p}` of its instance of {show(kind)} is driven by logic "
                               f"({len(hits)} bit{'s' if len(hits) > 1 else ''}); a child's input is driven by a "
                               "register, a child output, a module input or a constant")
    return bad


def show(name):
    """A module's name as the design wrote it (`$paramod\\gemm_row\\LGE=...` -> gemm_row)."""
    m = re.match(r"\$paramod(?:\$[0-9a-f]+)?\\([^\\]+)", name)
    return m.group(1) if m else name


def cut_text(mod, mods, table, clocks):
    """`mod`'s own cells as one flat netlist the ASAP7 view reads: its gates and assigns as they are, every child
    instance replaced by ports at its pins (a child's output becomes an input of the cut module, a child's input an
    output, bit by bit; clock pins and constant bits make no port)."""
    ports, decls, assigns, k = [], [], [], 0
    for n, d, w in mod.ports:
        ports.append(n)
    body_decls = []
    for n, d, w in mod.ports:
        rng = f"[{mod.widths[n][0]}:{mod.widths[n][1]}] " if n in mod.widths else ""
        body_decls.append(f"  {d} {rng}{n} ;")
    wires = []
    for n, (hi, lo) in mod.widths.items():
        if n not in {p[0] for p in mod.ports}:
            wires.append(f"  wire [{hi}:{lo}] {n} ;")
    for kind, inst, pins in mod.children:
        dirs = pin_dirs(mods, table, kind)
        cks = {"clk"} if kind in table else clocks[kind]
        for p, bits in sorted(pins.items()):
            if p in cks or p not in dirs:
                continue
            for b in bits:
                if b in ("0", "1", ppa.XBIT):
                    continue
                name = f"hcut{k}"
                k += 1
                ports.append(name)
                if dirs[p] == "output":
                    decls.append(f"  input {name} ;")
                    assigns.append(f"  assign {b} = {name};")
                else:
                    decls.append(f"  output {name} ;")
                    assigns.append(f"  assign {name} = {b};")
    return ("module cut (" + ", ".join(ports) + ");\n" + "\n".join(body_decls + wires + decls) + "\n"
            + "\n".join(g.strip("\n") for g in mod.gate_text) + "\n" + "\n".join(assigns) + "\nendmodule\n")


# ---------------------------------------------------------------------------------------------------- weighing
def open_asap7():
    pins = ppa.Pins(ppa.pdk_paths(PDK)[0])
    return ppa.Liberty(ppa.find_liberty(None, pins), pins), pins


def weigh_module(mod, mods, table, clocks, lib, pins):
    """The own cells of one module on the ASAP7 view: area (1e-5 um^2), period (ps), cells, flops. A module without
    a cell of its own (wiring only) weighs nothing unless its nets need buffers."""
    text = cut_text(mod, mods, table, clocks)
    if not mod.gates:
        return {"area_e5um2": 0, "period_ps": 0, "cells": 0, "flops": 0, "gates": 0, "wiring_only": True}
    try:
        a = ppa.analyze(text, lib, pins)
    except ppa.IllegalNetlist as e:
        raise HierError(f"module {show(mod.name)}: {' '.join(str(e).split())}")
    except ppa.PpaError as e:
        raise HierError(f"module {show(mod.name)}: the ASAP7 view cannot weigh it: {' '.join(str(e).split())}")
    return {"area_e5um2": a.area_e4, "period_ps": round(a.t_ns * 1000), "cells": a.cells, "flops": a.flops or 0,
            "gates": a.scored_gates, "critical": {"output": a.crit_output, "cells": a.crit_cells}}


def area_e5(text):
    return int((Decimal(str(text)) * 100000).to_integral_exact())


def compose(netlist_text, top, lib=None, pins=None, check_rule=True, progress=None):
    """The composed columns of a hierarchical netlist: per module and in total. Raises RuleError / HierError."""
    table, _ = sram_table()
    mods = read_netlist(netlist_text)
    if top not in mods:
        raise HierError(f"netlist: no module `{top}`")
    clocks = clock_ports(mods, table)
    if check_rule:
        bad = rule_findings(mods, table, top, clocks)
        if bad:
            raise RuleError(bad)
    if lib is None:
        lib, pins = open_asap7()
    counts, blocks = instance_counts(mods, table, top)
    rows, area, cells, flops, period, slowest = [], 0, 0, 0, 0, None
    for name in sorted(mods, key=lambda n: (show(n), n)):
        if not counts[name]:
            continue
        t0 = time.time()
        w = weigh_module(mods[name], mods, table, clocks, lib, pins)
        if progress:
            progress(f"hier: {show(name)}: {w['cells']} cells, {w['period_ps']} ps [{time.time() - t0:.1f} s]")
        rows.append({"module": show(name), "name": name, "instances": counts[name], **w})
        area += counts[name] * w["area_e5um2"]
        cells += counts[name] * w["cells"]
        flops += counts[name] * w["flops"]
        if w["period_ps"] > period:
            period, slowest = w["period_ps"], show(name)
    sram_rows, sram_area, sram_bits = [], 0, 0
    for kind in sorted(blocks):
        b = table[kind]
        sram_rows.append({"block": kind, "instances": blocks[kind], "area_e5um2": area_e5(b["area_um2"]),
                          "words": b["words"], "width": b["width"]})
        sram_area += blocks[kind] * area_e5(b["area_um2"])
        sram_bits += blocks[kind] * b["words"] * b["width"]
    return {"version": VERSION, "pdk": PDK, "ppa_version": pins.version, "ppa_pins_sha256": pins.sha256,
            "liberty_sha256": lib.sha256, "sram_table_sha256": score.sha256_file(SRAM_TABLE),
            "area_e5um2": area + sram_area, "area_um2": (area + sram_area) / 100000,
            "cells_area_e5um2": area, "sram_area_e5um2": sram_area, "sram_bits": sram_bits,
            "cells": cells, "flops": flops, "module_period_ps": period, "slowest_module": slowest,
            "modules": rows, "sram": sram_rows}


def flat_period(netlist_text, top, lib=None, pins=None):
    """The period of a FLAT netlist (the whole design at a small point), catalogue blocks cut at their pins."""
    table, _ = sram_table()
    mods = read_netlist(netlist_text)
    if list(mods) != [top]:
        raise HierError(f"netlist: expected the one flat module `{top}`, found {sorted(mods)}")
    if lib is None:
        lib, pins = open_asap7()
    w = weigh_module(mods[top], mods, table, clock_ports(mods, table), lib, pins)
    return {"period_ps": w["period_ps"], "cells": w["cells"], "flops": w["flops"], "critical": w.get("critical")}


def score_design(sources, top, params, work, check_rule=True, progress=None):
    """Synthesize with the hierarchy kept at `params` and compose. Returns the columns with the flow's facts."""
    netlist, facts = synthesize(sources, top, params, work)
    if progress:
        progress(f"hier: synthesized at {params} [{facts['seconds']} s]")
    with open(netlist) as fh:
        cols = compose(fh.read(), top, check_rule=check_rule, progress=progress)
    cols.update(params=dict(params), flow=facts, hier_script_sha256=score.sha256_file(os.path.abspath(__file__)))
    return cols


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="+")
    ap.add_argument("--top", required=True)
    ap.add_argument("--param", action="append")
    ap.add_argument("--flat", action="store_true", help="flatten (a small point): the flat period")
    ap.add_argument("--rules", action="store_true", help="the hierarchy rule only (no weighing)")
    ap.add_argument("--work")
    ap.add_argument("--json")
    args = ap.parse_args(argv)
    params = score.parse_params(args.param)
    work = os.path.abspath(args.work) if args.work else tempfile.mkdtemp(prefix="svgolf-hier-")
    say = lambda s: print(s, file=sys.stderr, flush=True)       # noqa: E731
    try:
        if args.flat:
            netlist, facts = synthesize(args.sources, args.top, params, work, flat=True)
            with open(netlist) as fh:
                res = {"flat": flat_period(fh.read(), args.top), "params": params, "flow": facts}
        elif args.rules:
            netlist, facts = synthesize(args.sources, args.top, params, work)
            table, _ = sram_table()
            with open(netlist) as fh:
                mods = read_netlist(fh.read())
            bad = rule_findings(mods, table, args.top)
            res = {"rule": "holds" if not bad else "fails", "findings": bad, "params": params,
                   "modules": sorted({show(n) for n in mods})}
            if bad:
                print(json.dumps(res, indent=2))
                return 1
        else:
            res = score_design(args.sources, args.top, params, work, progress=say)
    except HierError as e:
        print(json.dumps({"error": str(e), **({"findings": e.findings} if isinstance(e, RuleError) else {})}, indent=2))
        return 1
    finally:
        if not args.work:
            shutil.rmtree(work, ignore_errors=True)
    text = json.dumps(res, indent=2, sort_keys=True)
    print(text)
    if args.json:
        with open(args.json, "w") as fh:
            fh.write(text + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
