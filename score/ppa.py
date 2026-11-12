#!/usr/bin/env python3.12
"""svGolf PPA columns: area in um^2 and delay in ps on sky130_fd_sc_hd, from TWO flows side by side.

Flow A0' is the RANKED sky130 score (decided 2026-11-03: sky130 is the default library); the GE table and unit depth of score/score.py
(area_ge_v1, depth_v1, unchanged) are extra columns. Flow A1' is an unranked research column. Given a design and a task's
scoring point (or the scored netlist itself) it returns the columns, beside the unit depth the default scorer already reports.

Flow A0' (sky130_a0_v3: the repair and the per-task input drive of 2026-11-04), the block `ppa`:

  area_um2_sky130     sum of the sky130_fd_sc_hd cell areas of the REPAIRED netlist (flops and the tie cell included)
  delay_ps_sky130     latest primary-output arrival of a graph-based NLDM static timing analysis of it (integer ps)
  unit_depth          gates on the longest input-to-output path of the scored netlist (equal to `ltp -noff`, checked)

  A0' = the pinned flow's scored netlist (score.py, canon.ys, svgolf.ys, ge.json: all unchanged), each Yosys gate one _1
  cell, then REPAIRED BY BUFFERING ONLY (decided 2026-11-04: every netlist is repaired, by buffering; `repair`, the pins'
  `repair` and `constants` sections): every net over its driver's limits (internal nets, primary inputs driven by the
  task's input drive, flop Q nets, nets that drive output bits, each output BIT a separate 10 fF load) gets a balanced
  buffer tree within the liberty's limits, the tie cell is replicated within its max_capacitance, nothing is resized; the
  repaired netlist is written as structural Verilog, read back, simulated against the unrepaired one, and weighed with every
  primary input driven by the task's input drive and every output bit loaded with 10 fF. The input drive is a real cell
  in front of every input, its WHOLE delay counted: OpenSTA with one explicit instance of that cell per input gives the
  same arrivals to 1 fs. It is NOT OpenSTA's `set_driving_cell`, which adds only the drive's load-dependent delay,
  delay(load) - delay(0), and so is earlier by the zero-load delay (buf_1 at the 50 ps ramp: 58.7 ps on a rising input,
  72.8 ps on a falling one; `drive_arrival`). The input drive (sky130_a0_v3) is
  the task.json's `input_drive`, one of the pins' `timing.input_drive.allowed` (buf_N, inv_N, dfxtp_1's Q), else the pins'
  default sky130_fd_sc_hd__buf_8; a cell outside the list is a task-configuration error (TaskConfigError); the record's
  `setup.input_drive` names it. It must be ELECTRICALLY LEGAL: every load within its driver's
  max_capacitance (the tie cells' too), every transition within max_transition, every timing-table read inside the table's
  characterized grid. A netlist the repair cannot make legal is REJECTED (IllegalNetlist, naming the net in the design's
  words; check.py's `ppa` stage) and no number is reported: nothing is ever extrapolated (decided 2026-11-04:
  an illegal netlist is rejected outright). No wires. Bit-exact run to run (the repair is deterministic Python).
  Pins (liberty file, sha256, timing setup, the repair, gate-to-cell table, constant policy): score/ppa_pins.json.
  Loads per edge (sky130_a0_v3, 2026-11-04, before its release): a load pin presents its rise_capacitance to a rising transition
  and its fall_capacitance to a falling one, as OpenSTA reads them (the pins' `capacitance`, about their mean, was 0.5% to
  2.8% off OpenSTA on the references); max_capacitance and the repair's budgets take the larger edge. With that, the STA
  equals OpenSTA to 1 fs per arc (score/test_ppa_opensta.py records OpenSTA's numbers).

Flow A1', the sub-object `ppa.mapped`: the canonical RTLIL of the same run mapped by a REAL `abc -liberty` run onto
the policy-filtered liberty (compound cells, every drive strength; score/ppa_mapped.ys, pins in score/ppa_mapped_pins.json),
then weighed by the same STA and constants policy under its own, unchanged setup (sky130_a1_v1: no repair, no driving cell,
every input an ideal 50 ps ramp, no legality audit, linear extrapolation outside a table's grid; the 2026-11-04 ruling changed the
ranked flow, not this unranked research column):

  area_um2_sky130_mapped_v1   sum of the cell areas of the mapped netlist (um^2; `area_e4um2_sky130_mapped_v1` the integer)
  mapped_delay_sky130_v1      latest primary-output arrival of the same STA on the mapped netlist (integer ps)
  mapped_cells_sky130_v1, mapped_cell_hist_sky130_v1, mapped_levels_sky130_v1 (cell levels), buffers and inverters

  A1' is closer to a fabricated chip and more sensitive to the mapper (design/ppa/sky130.md: a median 12% in area and 49% in
  delay between ABC scripts; the proved array multiplier moves from 2nd to last in area). Its fields have their own names,
  version (`ppa_mapped_version`) and hashes and are never swapped silently with A0''s. The mapped netlist is simulated against
  the scored one on a fixed sample of input vectors before it is weighed. Bit-exact run to run (hash seeds, parallelism,
  temp directories: score/PPA.md).

Clocked netlists (`--seq`: score.py's clocked flow, every flop a $_DFF_P_): each flop is a dfxtp_1 cell (its area counts) and
cuts the timing graph; `delay_ps_sky130` is then the REGISTER-TO-REGISTER PERIOD of the repaired netlist (the flops' Q nets are
buffered too), the latest of every output arrival and every flop D arrival plus the liberty's setup, paths starting at the
inputs and at every Q at the liberty's clock-to-Q at the Q net's real load (ideal clock, transition pi_slew); the block says
`sequential: true` and `flops`. Ranked time for a clocked task = cycles x this period.

Study and measurements: design/ppa/sky130.md. What the numbers claim and do not claim: score/PPA.md.

The liberty (12.8 MB) is NOT vendored: it is fetched at a pinned sha256 (--fetch-liberty) into score/lib/ (git-ignored)
or taken from $SVGOLF_SKY130_LIB or --liberty. A missing file or a hash mismatch is an error, never a silent fallback.

ASAP7 (`--pdk asap7`, an ALTERNATIVE library beside sky130, which stays the default and unchanged): the same two flows
and the same principles (the scored netlist re-expressed cell by cell, repaired by buffering only, illegal netlists
rejected with the nets named, no extrapolation above a table's grid, bit-exact run to run) on asap7sc7p5t rev 28, RVT, TT
(0.70 V, 25 C), pinned in score/ppa_pins_asap7.json (flow A0', `asap7_a0_v1`) and score/ppa_mapped_pins_asap7.json +
score/ppa_mapped_asap7.ys (flow A1', `asap7_a1_v1`). Its columns carry their own names (`area_um2_asap7`,
`area_e5um2_asap7`, `delay_ps_asap7`, `cells_asap7`, `cell_hist_asap7`; A1': `area_um2_asap7_mapped_v1`, ...), never
the sky130 ones. What the library forces, each a pinned choice (the pins file says why): five liberty files instead of
one (fetched gzipped from ORFS at a pinned commit, both hashes checked; $SVGOLF_ASAP7_LIB or --liberty name a directory
holding them), ps/fF units (converted to ns/pF when read: every internal number is in the sky130 units), 5-decimal areas
(integers in 1e-5 um^2), cell names with a suffix, a Yosys gate that is two cells (MUX, ANDNOT, ORNOT: the library has
no such cell), a QN-only flop (an inverter forms Q), separate TIEHI/TIELO cells without a max_capacitance (the pins
state one), and table grids whose smallest load lies above many single pins: a read BELOW a grid (a load or an input
transition smaller than the library characterizes) is read at the grid's floor in that dimension and counted in
`legality.table_reads_floored` (MEASURED over every asap7 table the flow reads: the delays rise from their first point
along both axes, so a floored delay errs slow; the transitions rise along the load and are flat, within 0.39 ps, along
the input transition); above a grid the rule is sky130's (the repair buffers, else the netlist is rejected).

Usage:
  python3.12 score/ppa.py SOLUTION.sv --top TOP [--param N=16 ...]     # pinned flow, then weigh its netlist (A0') and map it (A1')
  python3.12 score/ppa.py SOLUTION.sv --task tasks/<name>               # top + scoring point from task.json
  python3.12 score/ppa.py --netlist-in SCORED.v                         # weigh an existing scored netlist (A0' only)
  python3.12 score/ppa.py --fetch-liberty                               # download the pinned liberty

Options:
  --json OUT       also write the result JSON to OUT
  --netlist OUT    (with a design) also write the scored netlist to OUT
  --mapped-netlist OUT   (with a design) also write the A1' mapped netlist to OUT
  --repaired-netlist OUT also write the repaired A0' netlist (structural Verilog: the buffer trees and tie cells) to OUT
  --no-mapped      A0' only: skip the mapping (no second Yosys run)
  --liberty PATH   the liberty file (default $SVGOLF_SKY130_LIB, else score/lib/<pinned name>); with
                   --fetch-liberty, where to put the download. With --pdk asap7: the DIRECTORY of the pinned files
                   (default $SVGOLF_ASAP7_LIB, else score/lib/asap7/)
  --pdk NAME       sky130 (the default: score/ppa_pins.json, the ranked columns) or asap7 (score/ppa_pins_asap7.json,
                   score/ppa_mapped_pins_asap7.json, score/ppa_mapped_asap7.ys: the asap7 columns)
  --pins PATH      a pins file (research and tests only: the result records its sha256)
  --path           also report the critical path (net names; and per node the driving cell, arrival and transition)
  --yosys PATH, --repeat K, --no-gate   as in score.py

  --latency L      (with --seq, or --netlist-in of a clocked netlist) the latency in cycles the design will declare:
                   the summary line then shows the ranked score, area x L cycles x period (a seq- or react-family
                   task's latency is 1 cycle)

Result JSON: {"ppa": {...columns..., "mapped": {...}}, "score": {...score.py's result, unchanged...}} for a design;
{"ppa": {...}} for --netlist-in. After it, ONE line on stderr (`summary_line`, never part of the JSON): the weighed area
and delay, `ppa (sky130 A0'): area 460.4416 um^2, delay 2611 ps; area x delay = 1202.21 um2*ns`; a clocked netlist's
`period` in place of the delay, and with --latency L `; score: A um^2 x L cycles x P ps = S um2*ns`
(leaderboard/combined.py's product, the ranked number of check.py's headline).
`ppa.mapped` is `{"available": false, "reason": ...}` for a design the mapping cannot weigh.
Exit status: 0 = weighed, 1 = refused or failed (missing, unreadable or wrong liberty, a cell outside the A0' table, an
undriven net, ..., synthesis failed, a netlist the repair cannot make legal, a repair or mapped netlist whose function differs
from the scored one), 2 = usage error.
"""

import argparse
import bisect
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from collections import defaultdict
from decimal import Decimal

HERE = os.path.dirname(os.path.abspath(__file__))
PINS_PATH = os.path.join(HERE, "ppa_pins.json")
LIB_DIR = os.path.join(HERE, "lib")
LIB_ENV = "SVGOLF_SKY130_LIB"
REPAIR_METHOD = "buffer_trees_v1"          # the repair this file implements (pins: repair.method)
TIE_POLICY = "replicated_within_max_capacitance"     # the constants policy it implements (pins: constants.policy)
NAND2_E4 = 37536     # sky130_fd_sc_hd__nand2_1 = 3.7536 um^2, the library's NAND2 (reported by the validation only)
# The libraries this file weighs on: (A0' pins, A1' pins, A1' script, the liberty's environment variable, its default
# location under score/lib/). sky130 is the default and the ranked one; asap7 is the alternative of `--pdk asap7`.
PDKS = {
    "sky130": ("ppa_pins.json", "ppa_mapped_pins.json", "ppa_mapped.ys", "SVGOLF_SKY130_LIB", None),
    "asap7": ("ppa_pins_asap7.json", "ppa_mapped_pins_asap7.json", "ppa_mapped_asap7.ys", "SVGOLF_ASAP7_LIB", "asap7"),
}
# liberty unit -> the divisor that brings a number in it to the internal unit (ns, pF: sky130's own)
TIME_UNITS = {"1ns": 1, "1ps": 1000}
CAP_UNITS = {"pf": 1, "ff": 1000}


def pdk_paths(pdk):
    """(A0' pins path, A1' pins path, A1' script path) of the library `pdk` (PDKS)."""
    if pdk not in PDKS:
        raise PpaError(f"unknown pdk {pdk!r} (one of {', '.join(PDKS)})")
    a, b, c = PDKS[pdk][:3]
    return os.path.join(HERE, a), os.path.join(HERE, b), os.path.join(HERE, c)


class PpaError(Exception):
    pass


class MappedDefect(PpaError):
    """The mapped netlist disagrees with the scored one in FUNCTION: not a property of the design but of the mapping flow or
    of this reader (the two readings of the same circuit differ), so `check.py --ppa require` makes it an infrastructure error,
    as it does a depth or gate-count disagreement of A0'."""


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ------------------------------------------------------------------------------------------------ pins
class Pins:
    """score/ppa_pins.json, validated."""

    def __init__(self, path=PINS_PATH):
        self.path = path
        try:
            with open(path) as fh:
                raw = json.load(fh)
        except (OSError, ValueError) as e:
            raise PpaError(f"cannot read the pins file {path}: {e}")
        self.sha256 = sha256_file(path)
        try:
            self.version = raw["ppa_version"]
            # the library (sky130 when the pins name none: score/ppa_pins.json predates the key) and the names its columns
            # carry: area_um2_<col>, delay_ps_<col>, ... (the integer area in 1e-<area_decimals> um^2)
            self.pdk = raw.get("pdk", "sky130")
            self.col = raw.get("column_suffix", "sky130")
            self.area_decimals = int(raw.get("area_decimals", 4))
            self.lib = dict(raw["liberty"])
            self.prefix = self.lib["cell_prefix"]
            self.suffix = self.lib.get("cell_suffix", "")
            # one liberty file (sky130: `file`, `sha256`, ...) or several (`files`, each with its own name and hashes)
            if "files" in self.lib:
                self.lib_files = [dict(f) for f in self.lib["files"]]
                for f in self.lib_files:
                    f["file"], f["sha256"], f["bytes"] = str(f["file"]), str(f["sha256"]), int(f["bytes"])
                self.multi = True
            else:
                self.lib_files = [{"file": self.lib["file"], "sha256": self.lib["sha256"],
                                   "bytes": self.lib.get("bytes"), "url": self.lib.get("url")}]
                self.multi = False
            t = raw["timing"]
            # ps -> ns and fF -> pF by one correctly-rounded division: identical to the literals 0.05 and 0.010
            self.pi_slew_ns = _per_1000(t["pi_slew_ps"], "timing.pi_slew_ps")
            self.po_load_pf = _per_1000(t["po_load_ff"], "timing.po_load_ff")
            self.pi_slew_ps, self.po_load_ff = t["pi_slew_ps"], t["po_load_ff"]       # as pinned, for the records
            # a timing-table read below the grid (a load or an input transition smaller than the library characterizes):
            # "reject" (sky130, where no single pin is below a grid) or "floor" (read at the grid's floor in that dimension)
            self.below_grid = t.get("below_grid", "reject")
            # the cell that drives every primary input (and whose limits the repair budgets): the task's `input_drive`
            # (task.json), one of `allowed`, else `default` (sky130_a0_v3)
            d = t["input_drive"]
            self.input_drive_default = d["default"]
            self.input_drives = list(d["allowed"])
            self.input_drive_shape = d.get("shape", r"(buf|inv)_\d+|" + FLOP_CELL)
            self.gates = {k: v for k, v in raw["gates"].items() if not k.startswith("_")}
            self.gate_cells = {k: _gate_cells(k, v) for k, v in self.gates.items()}
            c = raw["constants"]
            # one tie cell with both constants (sky130's conb_1: `cell`) or one cell per constant (`cells`: {"0", "1"})
            self.tie_cell = c.get("cell")
            self.tie_cells = ({"0": self.tie_cell, "1": self.tie_cell} if self.tie_cell is not None
                              else {"0": c["cells"]["0"], "1": c["cells"]["1"]})
            # the load a tie output may carry where its cell declares no max_capacitance (fF in the pins)
            self.tie_max_cap_pf = (_per_1000(c["max_capacitance_ff"], "constants.max_capacitance_ff")
                                   if "max_capacitance_ff" in c else None)
            self.tie_policy = c["policy"]
            if self.tie_policy != TIE_POLICY:
                raise PpaError(f"only the constants policy {TIE_POLICY!r} is implemented")
            # the clocked flow's one flop ($_DFF_P_); sky130's when the pins name none. `q_inverter`: the cell that forms
            # Q from a flop that has only an inverted output (asap7's DFFHQNx1)
            fl = raw.get("flop", {"cell": FLOP_CELL, "clock": "CLK", "d": "D", "q": "Q"})
            self.flop = {"cell": fl["cell"], "clock": fl["clock"], "d": fl["d"], "q": fl["q"],
                         "q_inverter": dict(fl["q_inverter"]) if fl.get("q_inverter") else None}
            self.flop_cell = self.flop["cell"]
            # the cell classes (`cell_class`): only class "logic" may appear in a weighed netlist
            self.policy = [tuple(x) for x in raw["cell_policy"]] if "cell_policy" in raw else POLICY
            r = raw["repair"]
            self.repair_method = r["method"]
            self.repair_buffers = list(r["buffers"])
            self.repair_max_rounds = int(r["max_rounds"])
            self.repair_vectors = int(r["equivalence"]["vectors"])
            self.repair_seed = r["equivalence"]["seed"]
        except (KeyError, TypeError, ValueError) as e:
            raise PpaError(f"pins file {path}: missing or malformed key {e}")
        units = self.lib.get("units") if isinstance(self.lib.get("units"), dict) else {}
        if units.get("time") not in TIME_UNITS or units.get("capacitance") not in CAP_UNITS:
            raise PpaError(f"pins file {path}: liberty.units must name a time unit of {sorted(TIME_UNITS)} and a "
                           f"capacitance unit of {sorted(CAP_UNITS)}")
        if self.below_grid not in ("reject", "floor"):
            raise PpaError(f"pins file {path}: timing.below_grid must be \"reject\" or \"floor\"")
        if self.area_decimals < 0 or self.area_decimals > 9:
            raise PpaError(f"pins file {path}: area_decimals must be 0 to 9")
        if self.repair_method != REPAIR_METHOD:
            raise PpaError(f"pins file {path}: repair.method {self.repair_method!r} is not this ppa.py's {REPAIR_METHOD!r}")
        if not self.repair_buffers or len(set(self.repair_buffers)) != len(self.repair_buffers):
            raise PpaError(f"pins file {path}: repair.buffers must name at least one buffer cell, each once")
        if self.repair_vectors < 256 or self.repair_vectors % 256 or self.repair_max_rounds < 1:
            raise PpaError(f"pins file {path}: repair.equivalence.vectors must be a positive multiple of 256 and "
                           "repair.max_rounds positive")
        shapes = [c for c in self.input_drives if not (isinstance(c, str) and c.startswith(self.prefix)
                  and c.endswith(self.suffix) and re.fullmatch(self.input_drive_shape, self.short(c)))]
        if (not self.input_drives or len(set(self.input_drives)) != len(self.input_drives) or shapes
                or self.input_drive_default not in self.input_drives):
            raise PpaError(f"pins file {path}: timing.input_drive.allowed must name each cell once, every one a "
                           f"{self.full('<' + self.input_drive_shape + '>')} cell, and contain "
                           "timing.input_drive.default")

    def lib_file(self):
        """The liberty's file name (several libraries: their names joined by `+`, for messages and records)."""
        return self.lib["file"] if not self.multi else "+".join(f["file"] for f in self.lib_files)

    def full(self, short):
        """The liberty name of a cell the pins name short: `inv_1` -> `sky130_fd_sc_hd__inv_1`, `INVx1` ->
        `INVx1_ASAP7_75t_R`."""
        return self.prefix + short + self.suffix

    def short(self, name):
        """The pins' short name of a liberty cell (the inverse of `full`; a name of another shape is returned as it is)."""
        if name.startswith(self.prefix) and name.endswith(self.suffix) and len(name) > len(self.prefix) + len(self.suffix):
            return name[len(self.prefix):len(name) - len(self.suffix)]
        return name


def _per_1000(x, what):
    """A pinned ps or fF number as ns or pF: one correctly-rounded division by 1000 (an integer pin, as sky130's 50 and 10,
    gives exactly what it always gave)."""
    if isinstance(x, bool) or not isinstance(x, (int, float)) or not x > 0:
        raise PpaError(f"pins: {what} must be a positive number")
    return x / 1000


def _gate_cells(gate, ent):
    """A gate-table entry as the list of cells that build the Yosys gate, [(cell, {cell input pin: signal}, cell output
    pin, output signal)], in order; a signal is a pin of the generic gate (A, B, S) or the output of an earlier cell of
    the list, and the last cell drives Y. One cell (sky130, `{"cell", "pins": {gate pin: cell pin}, "out"}`) or a short
    list (`{"cells": [{"cell", "conn": {cell input pin: signal}, "out": {cell output pin: signal}}, ...]}`, for a library
    without a one-cell build of the gate)."""
    if gate not in GATE_SEMANTICS:
        raise PpaError(f"pins: gate {gate} is not a Yosys abc -g gate")
    if "cells" not in ent:
        return [(ent["cell"], {cp: gp for gp, cp in ent["pins"].items()}, ent["out"], "Y")]
    out, defined = [], set()
    ins = set(GATE_SEMANTICS[gate][0])
    for k, c in enumerate(ent["cells"]):
        (op, sig), = c["out"].items()
        bad = [s for s in c["conn"].values() if s not in ins and s not in defined]
        if bad or sig in ins or sig in defined or (sig == "Y") != (k == len(ent["cells"]) - 1):
            raise PpaError(f"pins: gate {gate}: cell {k} ({c['cell']}) reads an undefined signal {bad} or defines "
                           f"{sig!r} out of order (internal signals once each, before use; Y by the last cell only)")
        defined.add(sig)
        out.append((c["cell"], dict(c["conn"]), op, sig))
    used = {s for _, conn, _, _ in out for s in conn.values()}
    if not ins <= used or not (defined - {"Y"}) <= used:
        raise PpaError(f"pins: gate {gate}: every input of the gate and every internal signal must be read")
    return out


class TaskConfigError(PpaError):
    """A task's `input_drive` (task.json) is not a cell of the pins' `timing.input_drive.allowed`: a defect of the task's
    configuration, never a property of a design (check.py: an infrastructure error; tests/run.py's layout step)."""


def input_drive_of(task, pins):
    """The cell that drives every primary input of `task` (its task.json object, or None for a netlist of no task): its
    `input_drive`, else the pins' default (sky130_a0_v3). TaskConfigError unless it is one of the pins' allowed cells."""
    if task is None or "input_drive" not in task:
        return check_input_drive(pins.input_drive_default, pins, "the pins' timing.input_drive.default")
    return check_input_drive(task["input_drive"], pins, f"task {task.get('name', '?')}: input_drive")


def check_input_drive(name, pins, what="input_drive"):
    """`name` if it is one of the pins' allowed input drives, else TaskConfigError naming `what` and the allowed cells."""
    if not isinstance(name, str) or name not in pins.input_drives:
        raise TaskConfigError(f"{what} {name!r} is not one of the allowed input drives ({', '.join(pins.input_drives)}; "
                              "score/ppa_pins.json timing.input_drive)")
    return name


# ------------------------------------------------------------------------------------------------ liberty
_TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][\w.\[\]$]*|-?[\d.]+(?:[eE][-+]?\d+)?|[{}():;,]')
# `cell ("name") {` (sky130) or `cell (name) {` (asap7)
_CELL_RE = re.compile(r'^[ \t]*cell[ \t]*\([ \t]*(?:"([^"]*)"|([A-Za-z_][\w$]*))[ \t]*\)[ \t]*\{', re.M)
_BRACE_RE = re.compile(r'"(?:[^"\\]|\\.)*"|[{}]')
# a simple attribute alone on its line without its closing semicolon (`area : 0.04374`: all 37 cells of asap7's INVBUF
# files, five of its SEQ file): the line end closes it, as Yosys and OpenSTA read it. sky130 has no such line, so its
# reading is unchanged (test_ppa_asap7.py checks the count is 0 there).
_NOSEMI_RE = re.compile(r'^([ \t]*[A-Za-z_]\w*[ \t]*:[ \t]*[^;{}\n]*[^;{}\s])[ \t]*$', re.M)


class _Group:
    __slots__ = ("kind", "args", "attrs", "children")

    def __init__(self, kind, args):
        self.kind, self.args, self.attrs, self.children = kind, args, {}, []

    def find(self, kind):
        return [c for c in self.children if c.kind == kind]


def _unq(t):
    return t[1:-1] if t.startswith('"') else t


def _group_body(toks, pos, g):
    n = len(toks)
    while pos < n and toks[pos] != "}":
        name = toks[pos]
        pos += 1
        t = toks[pos]
        if t == ":":
            pos += 1
            val = []
            while toks[pos] != ";":
                val.append(_unq(toks[pos]))
                pos += 1
            pos += 1
            g.attrs[name] = val[0] if len(val) == 1 else val
        elif t == "(":
            pos += 1
            args = []
            while toks[pos] != ")":
                if toks[pos] != ",":
                    args.append(_unq(toks[pos]))
                pos += 1
            pos += 1
            if pos < n and toks[pos] == "{":
                c = _Group(name, args)
                pos = _group_body(toks, pos + 1, c) + 1
                g.children.append(c)
            else:
                if toks[pos] == ";":
                    pos += 1
                g.attrs[name] = args
        else:
            pos += 1
    return pos


def _parse_group_text(text):
    """The single group `name ( args ) { ... }` that `text` consists of."""
    toks = _TOKEN.findall(_NOSEMI_RE.sub(r"\1;", re.sub(r"\\\s*\n", " ", text)))
    if len(toks) < 4 or toks[1] != "(":
        raise PpaError("liberty: malformed group")
    pos = 2
    args = []
    while toks[pos] != ")":
        if toks[pos] != ",":
            args.append(_unq(toks[pos]))
        pos += 1
    if toks[pos + 1] != "{":
        raise PpaError("liberty: group without a body")
    g = _Group(toks[0], args)
    _group_body(toks, pos + 2, g)
    return g


def _num(x, div):
    """A liberty number in the internal unit: `div` is the divisor of its unit (TIME_UNITS, CAP_UNITS; 1 for sky130, whose
    numbers are read exactly as before)."""
    return float(x) if div == 1 else float(x) / div


class Table:
    """A 2-D NLDM table: index_1 = input transition (ns), index_2 = output load (pF). `d1`, `d2`, `dv`: the divisors that
    bring index_1, index_2 and the values from the liberty's units to ns and pF (`_num`). `transpose`: the table is stored
    the other way round (asap7's setup tables: index_1 the constrained pin's transition, index_2 the clock's), so that i1 is
    always what the caller reads first."""
    __slots__ = ("i1", "i2", "v")

    def __init__(self, g, what, d1=1, d2=1, dv=1, transpose=False):
        if "index_1" not in g.attrs or "index_2" not in g.attrs:
            raise PpaError(f"liberty: {what} is not a 2-D table (the A0' timing needs index_1 and index_2)")
        self.i1 = [_num(x, d1) for x in g.attrs["index_1"][0].split(",")]
        self.i2 = [_num(x, d2) for x in g.attrs["index_2"][0].split(",")]
        rows = g.attrs["values"]
        self.v = [[_num(x, dv) for x in row.split(",")] for row in rows]
        if (len(self.v) != len(self.i1) or any(len(r) != len(self.i2) for r in self.v)
                or len(self.i1) < 2 or len(self.i2) < 2
                or self.i1 != sorted(self.i1) or self.i2 != sorted(self.i2)):
            raise PpaError(f"liberty: {what} has inconsistent indices and values")
        if transpose:
            self.i1, self.i2 = self.i2, self.i1
            self.v = [list(col) for col in zip(*self.v)]

    def covers(self, x1, x2):
        """The point lies inside the characterized grid (bounds included)."""
        return self.i1[0] <= x1 <= self.i1[-1] and self.i2[0] <= x2 <= self.i2[-1]

    def clamp(self, x1, x2):
        return min(max(x1, self.i1[0]), self.i1[-1]), min(max(x2, self.i2[0]), self.i2[-1])

    def at(self, x1, x2):
        """Bilinear interpolation INSIDE the characterized grid. A point outside it is never extrapolated (sky130_a0_v2,
        decided 2026-11-04: the extrapolated tables are non-monotone and go negative): TableRange. The STA reads through `_read`,
        which records such a point in its Audit instead, so that the weighing rejects the netlist with every violation
        named. (`_bilinear` itself extrapolates linearly outside the grid: flow A1''s unchanged reading, A1_EXTRAPOLATES.)"""
        if not self.covers(x1, x2):
            raise TableRange(f"a timing table read at ({x1:.6g} ns, {x2:.6g} pF) outside its characterized range "
                             f"[{self.i1[0]:g}, {self.i1[-1]:g}] ns x [{self.i2[0]:g}, {self.i2[-1]:g}] pF")
        return self._bilinear(x1, x2)

    def _bilinear(self, x1, x2):
        def locate(idx, x):
            k = bisect.bisect_right(idx, x) - 1
            k = max(0, min(len(idx) - 2, k))
            return k, (x - idx[k]) / (idx[k + 1] - idx[k])
        a, ta = locate(self.i1, x1)
        b, tb = locate(self.i2, x2)
        v = self.v
        top = v[a][b] * (1 - tb) + v[a][b + 1] * tb
        bot = v[a + 1][b] * (1 - tb) + v[a + 1][b + 1] * tb
        return top * (1 - ta) + bot * ta


class TableRange(PpaError):
    """A timing or power table read outside its characterized index range (nothing is extrapolated)."""


_TABLES = ("cell_rise", "cell_fall", "rise_transition", "fall_transition")


class Arc:
    """A timing arc related_pin -> output pin with its four tables."""
    __slots__ = ("related", "sense", "tbl")

    def __init__(self, g, cell, pin, templates, tdiv=1, cdiv=1):
        self.related = g.attrs.get("related_pin")
        self.sense = g.attrs.get("timing_sense", "non_unate")
        what = f"{cell} arc {self.related}->{pin}"
        if self.related is None:
            raise PpaError(f"liberty: {what}: no related_pin")
        if g.attrs.get("timing_type", "combinational") != "combinational":
            raise PpaError(f"liberty: {what}: timing_type {g.attrs['timing_type']!r} is not combinational")
        if self.sense not in ("positive_unate", "negative_unate", "non_unate"):
            raise PpaError(f"liberty: {what}: unknown timing_sense {self.sense!r}")
        self.tbl = delay_tables(g, what, templates, tdiv, cdiv)


def delay_tables(g, what, templates, tdiv=1, cdiv=1):
    """{table name: Table} of the four delay and transition tables of timing group `g`, each on the template
    (input_net_transition, total_output_net_capacitance), read in ns and pF."""
    tbl = {}
    for k in _TABLES:
        found = g.find(k)
        if len(found) != 1:
            raise PpaError(f"liberty: {what}: expected one {k} table, found {len(found)}")
        tg = found[0]
        tpl = templates.get(tg.args[0] if tg.args else None)
        if tpl != ("input_net_transition", "total_output_net_capacitance"):
            raise PpaError(f"liberty: {what}: table {k} has template {tg.args} whose variables are "
                           f"{tpl}, not (input_net_transition, total_output_net_capacitance)")
        tbl[k] = Table(tg, f"{what} {k}", tdiv, cdiv, tdiv)
    return tbl


def edge_caps(p, cdiv=1):
    """{"r": rise_capacitance, "f": fall_capacitance} of a liberty input pin group (its `capacitance` where one is not
    declared), in pF. A load pin presents its rise_capacitance to a rising transition and its fall_capacitance to a falling
    one, as OpenSTA reads them; sky130_fd_sc_hd's `capacitance` is about their mean (rise about 4.7% above it, fall 4.7%
    below, at most 9%), and timing at it was 0.5% to 2.8% off OpenSTA on the references (MEASURED 2026-11-04,
    test_ppa_opensta.py)."""
    c = p.attrs.get("capacitance", 0.0)
    return {"r": _num(p.attrs.get("rise_capacitance", c), cdiv), "f": _num(p.attrs.get("fall_capacitance", c), cdiv)}


class Cell:
    def __init__(self, g, templates, tdiv=1, cdiv=1, decimals=4):
        self.name = g.args[0]
        self.area_e4 = _area_e4(g.attrs.get("area"), self.name, decimals)    # in 1e-<decimals> um^2 (sky130: 1e-4)
        self.pin_cap, self.inputs, self.outputs = {}, [], []
        self.pin_cap_e = {}                        # {pin: {"r": rise_capacitance, "f": fall_capacitance}}: what timing reads
        self.function, self.arcs = {}, {}
        self.max_cap, self.max_trans = {}, {}      # the pins' max_capacitance (outputs) and max_transition, where declared
        for p in g.find("pin"):
            pn, direction = p.args[0], p.attrs.get("direction")
            if "max_transition" in p.attrs:
                self.max_trans[pn] = _num(p.attrs["max_transition"], tdiv)
            if direction == "input":
                self.inputs.append(pn)
                self.pin_cap[pn] = _num(p.attrs.get("capacitance", 0.0), cdiv)
                self.pin_cap_e[pn] = edge_caps(p, cdiv)
            elif direction == "output":
                self.outputs.append(pn)
                self.function[pn] = p.attrs.get("function")
                self.arcs[pn] = [Arc(t, self.name, pn, templates, tdiv, cdiv) for t in p.find("timing")]
                if "max_capacitance" in p.attrs:
                    self.max_cap[pn] = _num(p.attrs["max_capacitance"], cdiv)


def _area_e4(s, name, decimals=4):
    """A cell's area as an integer in 1e-`decimals` um^2 (sky130: 1e-4, asap7: 1e-5), refused if it has more decimals."""
    try:
        d = Decimal(s) * (10 ** decimals)
    except Exception:
        raise PpaError(f"liberty: cell {name}: no usable area ({s!r})")
    if d != d.to_integral_value():
        raise PpaError(f"liberty: cell {name}: area {s} has more than {decimals} decimals")
    return int(d)


def lib_env(pins):
    """The environment variable naming the liberty of `pins`' library ($SVGOLF_SKY130_LIB, $SVGOLF_ASAP7_LIB)."""
    return PDKS.get(pins.pdk, PDKS["sky130"])[3]


def default_liberty(pins):
    """Where --fetch-liberty puts the pinned liberty and where it is looked for by default: score/lib/<file> (one file) or
    score/lib/<pdk>/ (several, a directory)."""
    if pins.multi:
        return os.path.join(LIB_DIR, PDKS.get(pins.pdk, (None,) * 5)[4] or pins.pdk)
    return os.path.join(LIB_DIR, pins.lib_file())


def find_liberty(explicit=None, pins=None):
    """The liberty path to use (it need not exist): explicit > $SVGOLF_SKY130_LIB ($SVGOLF_ASAP7_LIB) > score/lib/<pinned
    name> (score/lib/asap7/, a directory, for a library of several files)."""
    if explicit:
        return explicit
    pins = pins or Pins()
    env = os.environ.get(lib_env(pins))
    if env:
        return env
    return default_liberty(pins)


def set_sha256(files):
    """The identity of a library of several files: SHA-256 over `<file name> <sha256>\\n` per file, in the pins' order."""
    return sha256_bytes("".join(f"{f['file']} {f['sha256']}\n" for f in files).encode())


class Liberty:
    """The pinned liberty: sha256 verified at load, cells parsed lazily (the 12.8 MB file is scanned once for the
    cell spans, about 0.1 s; a cell is tokenized only when asked for). A library of several files (asap7: `path` is the
    directory holding them) is read file by file, each verified against its own pinned sha256, its own header (units,
    templates, default_max_transition) applying to its own cells; cell names are unique across the files."""

    def __init__(self, path, pins):
        self.path, self.pins = path, pins
        if pins.multi:
            if not os.path.isdir(path):
                raise PpaError(f"liberty directory not found: {path}\n  fetch the pinned files with `python3.12 "
                               f"score/ppa.py --pdk {pins.pdk} --fetch-liberty` (into {default_liberty(pins)}), or "
                               f"point ${lib_env(pins)} / --liberty at a directory holding them")
            self.paths = [os.path.join(path, f["file"]) for f in pins.lib_files]
        else:
            self.paths = [path]
        self.tdiv = TIME_UNITS[pins.lib["units"]["time"]]
        self.cdiv = CAP_UNITS[pins.lib["units"]["capacitance"]]
        self.decimals = pins.area_decimals
        self._texts, self._start, self._templates, self.dmts, self.file_of = [], {}, [], [], {}
        names = []
        for k, (p, f) in enumerate(zip(self.paths, pins.lib_files)):
            if not os.path.isfile(p):
                raise PpaError(f"liberty not found: {p}\n  fetch the pinned file with `python3.12 score/ppa.py "
                               + ("" if pins.pdk == "sky130" else f"--pdk {pins.pdk} ")
                               + f"--fetch-liberty` (into score/lib/), or point ${lib_env(pins)} / --liberty at a copy "
                               f"(sha256 {f['sha256']})")
            try:
                with open(p, "rb") as fh:
                    data = fh.read()
            except OSError as e:     # a file that exists but cannot be read: a PpaError, not a traceback
                raise PpaError(f"liberty {p}: cannot be read: {e}")
            got = sha256_bytes(data)
            if got != f["sha256"]:
                raise PpaError(f"liberty {p}: sha256 {got} is not the pinned {f['sha256']}")
            try:
                text = re.sub(r"/\*.*?\*/", "", data.decode("ascii"), flags=re.S)
            except UnicodeDecodeError as e:
                raise PpaError(f"liberty {p}: not an ASCII file ({e})")
            spans = [(m.start(), m.group(1) if m.group(1) is not None else m.group(2)) for m in _CELL_RE.finditer(text)]
            if not spans:
                raise PpaError(f"liberty {p}: no cell groups found")
            fnames = [n for _, n in spans]
            if len(set(fnames)) != len(fnames) or set(fnames) & set(names):
                raise PpaError(f"liberty {p}: duplicate cell names")
            names += fnames
            self._texts.append(text)
            for s, n in spans:
                self._start[n] = s
                self.file_of[n] = k
            header = _parse_group_text(text[:spans[0][0]] + "}")
            self._check_units(header, p)
            dmt = header.attrs.get("default_max_transition")
            self.dmts.append(_num(dmt, self.tdiv) if dmt is not None else None)    # a pin without its own max_transition
            self._templates.append({t.args[0]: (t.attrs.get("variable_1"), t.attrs.get("variable_2"))
                                    for t in header.find("lu_table_template")})
        # one file: its sha256 (sky130, as always); several: the set's identity (`set_sha256`), each file's in `file_sha256`
        self.file_sha256 = {f["file"]: f["sha256"] for f in pins.lib_files}
        self.sha256 = pins.lib_files[0]["sha256"] if not pins.multi else set_sha256(pins.lib_files)
        self.cell_names = sorted(names)
        # one file: its text and templates as single values (energy.py, derive_seq_prices.py and the tests read them)
        self._text = self._texts[0] if not pins.multi else None
        self.templates = self._templates[0] if not pins.multi else None
        # the library's default_max_transition: its file's (one file), else the SMALLEST the files declare. asap7 declares
        # 320 ps in four files and 4000 ps in SIMPLE_RVT_TT (a characterization artifact: the same file's FF
        # re-characterization says 320, every input pin of every file declares max_transition 320 and every table's
        # transition axis ends at 320), so its limit is 320 ps for every cell.
        declared = [x for x in self.dmts if x is not None]
        self.default_max_transition = (self.dmts[0] if not pins.multi else (min(declared) if declared else None))
        self._cache = {}

    def _check_units(self, g, path=None):
        want = self.pins.lib["units"]
        cap = g.attrs.get("capacitive_load_unit")
        got = {"time": g.attrs.get("time_unit"), "voltage": g.attrs.get("voltage_unit"),
               "capacitance": (cap[1].lower() if isinstance(cap, list) and len(cap) == 2
                               and float(cap[0]) == 1.0 else None)}
        if got != want:
            raise PpaError(f"liberty units {got} differ from the pinned {want}"
                           + (f" ({os.path.basename(path)})" if self.pins.multi and path else ""))

    def has(self, name):
        return name in self._start

    def group(self, name):
        """The parsed liberty group of cell `name`."""
        if name not in self._start:
            raise PpaError(f"the liberty has no cell {name}")
        text = self._texts[self.file_of[name]]
        start = self._start[name]
        depth = 0
        end = None
        for m in _BRACE_RE.finditer(text, text.index("{", start)):
            c = m.group(0)
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    end = m.end()
                    break
        if end is None:
            raise PpaError(f"liberty: unbalanced braces in cell {name}")
        return _parse_group_text(text[start:end])

    def templates_of(self, name):
        """The lu_table_templates of the file that holds cell `name`."""
        return self._templates[self.file_of[name]]

    def cell(self, name):
        if name not in self._cache:
            self._cache[name] = Cell(self.group(name), self.templates_of(name), self.tdiv, self.cdiv, self.decimals)
        return self._cache[name]


def fetch_liberty(dest=None, pins=None):
    """Download the pinned liberty to `dest` (default score/lib/<pinned name>; a library of several files: the directory
    score/lib/<pdk>/), verifying size and sha256 before each file is moved into place (a file pinned with a `gz_url` is
    fetched gzipped, its compressed size and sha256 checked, then decompressed and checked again). Returns the path. An
    existing file with the right hash is left alone."""
    pins = pins or Pins()
    dest = dest or default_liberty(pins)
    if not pins.multi:
        _fetch_one(pins.lib_files[0], dest)
        return dest
    os.makedirs(dest, exist_ok=True)
    for f in pins.lib_files:
        _fetch_one(f, os.path.join(dest, f["file"]))
    return dest


def _fetch_one(f, dest):
    import gzip
    if os.path.isfile(dest) and sha256_file(dest) == f["sha256"]:
        return dest
    os.makedirs(os.path.dirname(os.path.abspath(dest)), exist_ok=True)
    fd, part = tempfile.mkstemp(prefix=os.path.basename(dest) + ".", suffix=".part", dir=os.path.dirname(os.path.abspath(dest)))
    try:
        url = f.get("gz_url") or f["url"]
        print(f"downloading {url}", file=sys.stderr)
        with urllib.request.urlopen(url, timeout=120) as resp, os.fdopen(fd, "wb") as out:
            shutil.copyfileobj(resp, out)
        if f.get("gz_url"):
            if os.path.getsize(part) != f["gz_bytes"] or sha256_file(part) != f["gz_sha256"]:
                raise PpaError(f"the downloaded file is not the pinned {os.path.basename(url)} (size "
                               f"{os.path.getsize(part)}, sha256 {sha256_file(part)}; pinned {f['gz_bytes']} bytes, "
                               f"{f['gz_sha256']})")
            with open(part, "rb") as fh:
                raw = gzip.decompress(fh.read())
            with open(part, "wb") as fh:
                fh.write(raw)
        if os.path.getsize(part) != f["bytes"] or sha256_file(part) != f["sha256"]:
            raise PpaError(f"the downloaded file is not the pinned liberty (size {os.path.getsize(part)}, "
                           f"sha256 {sha256_file(part)}; pinned {f['bytes']} bytes, {f['sha256']})")
        os.chmod(part, 0o644)
        os.replace(part, dest)
    except (OSError, EOFError) as e:
        raise PpaError(f"cannot fetch the liberty: {e}")
    finally:
        if os.path.exists(part):
            os.remove(part)
    return dest


# ------------------------------------------------------------------------------------------------ boolean functions
_FTOK = re.compile(r"[A-Za-z_]\w*|[!&|^()*+']|\s+")


def _compile_function(expr):
    """Liberty boolean function -> Python expression over `v` (pin -> int bit-vector) and the mask `M`."""
    toks = [t for t in _FTOK.findall(expr) if not t.isspace()]
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def p_or():
        nonlocal pos
        l = p_xor()
        while peek() in ("|", "+"):
            pos += 1
            l = f"({l} | {p_xor()})"
        return l

    def p_xor():
        nonlocal pos
        l = p_and()
        while peek() == "^":
            pos += 1
            l = f"({l} ^ {p_and()})"
        return l

    def p_and():
        nonlocal pos
        l = p_not()
        while peek() in ("&", "*"):
            pos += 1
            l = f"({l} & {p_not()})"
        return l

    def p_not():
        nonlocal pos
        if peek() == "!":
            pos += 1
            return f"(M ^ {p_not()})"
        a = p_atom()
        while peek() == "'":
            pos += 1
            a = f"(M ^ {a})"
        return a

    def p_atom():
        nonlocal pos
        t = peek()
        pos += 1
        if t == "(":
            e = p_or()
            if peek() != ")":
                raise PpaError(f"liberty function {expr!r}: missing )")
            pos += 1
            return e
        if t is None or not re.fullmatch(r"[A-Za-z_]\w*", t):
            raise PpaError(f"liberty function {expr!r}: unexpected {t!r}")
        return f"v[{t!r}]"

    out = p_or()
    if pos != len(toks):
        raise PpaError(f"liberty function {expr!r}: trailing {toks[pos:]}")
    return out


def eval_function(expr, v, mask):
    return eval(_compile_function(expr), {"__builtins__": {}}, {"v": v, "M": mask})


# Yosys `abc -g` gate semantics (the cells of $_X_ with pins A, B, S, Y), bit-parallel over a mask M
GATE_SEMANTICS = {
    "NOT":    (("A",), lambda a, M: M ^ a[0]),
    "AND":    (("A", "B"), lambda a, M: a[0] & a[1]),
    "NAND":   (("A", "B"), lambda a, M: M ^ (a[0] & a[1])),
    "OR":     (("A", "B"), lambda a, M: a[0] | a[1]),
    "NOR":    (("A", "B"), lambda a, M: M ^ (a[0] | a[1])),
    "XOR":    (("A", "B"), lambda a, M: a[0] ^ a[1]),
    "XNOR":   (("A", "B"), lambda a, M: M ^ (a[0] ^ a[1])),
    "ANDNOT": (("A", "B"), lambda a, M: a[0] & (M ^ a[1])),
    "ORNOT":  (("A", "B"), lambda a, M: a[0] | (M ^ a[1])),
    "MUX":    (("A", "B", "S"), lambda a, M: (a[0] & (M ^ a[2])) | (a[1] & a[2])),     # S ? B : A
}


def check_gate_cell(lib, pins, gate):
    """The liberty cell chosen for Yosys gate `gate` computes that gate (truth table over all inputs), through the
    pin map of the pins file. Raises PpaError otherwise: a wrong pin map would silently change every number."""
    ins, sem = GATE_SEMANTICS[gate]
    n = len(ins)
    rows = 1 << n
    mask = (1 << rows) - 1
    vec = {p: sum(1 << r for r in range(rows) if (r >> i) & 1) for i, p in enumerate(ins)}
    want = sem([vec[p] for p in ins], mask)
    sig = dict(vec)                     # signal -> truth table: the gate's inputs, then each cell's output (a 2-cell build)
    names = []
    for cname, cpins, out, osig in pins.gate_cells[gate]:
        cell = lib.cell(pins.full(cname))
        names.append(cell.name)
        fn = cell.function.get(out)
        if fn is None:
            raise PpaError(f"liberty cell {cell.name} has no function on output {out}")
        if set(cpins) != set(cell.inputs):
            raise PpaError(f"liberty cell {cell.name}: the pin map of {gate} connects {sorted(cpins)}, the cell's inputs "
                           f"are {sorted(cell.inputs)}")
        env = {cp: sig[s] for cp, s in cpins.items()}
        try:
            sig[osig] = eval_function(fn, env, mask)
        except KeyError as e:
            raise PpaError(f"liberty cell {cell.name}: function {fn!r} reads pin {e}, not in the pin map of {gate}")
    if sig["Y"] != want:
        ent = pins.gates[gate]
        fns = " ; ".join(repr(lib.cell(x).function.get(o)) for x, (_, _, o, _) in zip(names, pins.gate_cells[gate]))
        raise PpaError(f"liberty cell {' + '.join(names)} (function {fns}) does not compute the Yosys gate ${gate}$ "
                       f"through the pin map {ent.get('pins', ent.get('cells'))}")


# The cell policy of the study (sky130.md section 4): only class "logic" may appear in a weighed netlist.
POLICY = [
    (r"^lpflow_", "low-power-flow"),
    (r"^(fill|decap|tap|diode|probe|probec_p|macro_sparecell)", "physical-only"),
    (r"^(df|sdf|edf|sedf)", "sequential"),
    (r"^(dl[rx]|sdlclkp|dlclkp)", "sequential"),
    (r"^dly", "delay"),
    (r"^clk", "clock"),
    (r"^(ebufn|einvn|einvp)", "tristate"),
    (r"^(fa|fah|fahcin|fahcon|ha)_", "multi-output"),
    (r"^conb_", "tie"),
]


def cell_class(name, prefix="sky130_fd_sc_hd__", policy=None, suffix=""):
    """The class of liberty cell `name` under `policy` (the pins' `cell_policy`; sky130's POLICY by default), matched on
    the name without the library's prefix and suffix."""
    n = name[len(prefix):] if name.startswith(prefix) else name
    if suffix and n.endswith(suffix):
        n = n[:-len(suffix)]
    for pat, cls in (POLICY if policy is None else policy):
        if re.search(pat, n):
            return cls
    return "logic"


def pins_class(name, pins):
    """`cell_class` under the pins' library: its prefix, suffix and cell policy (sky130's: the call as it always was)."""
    if pins.policy is POLICY and not pins.suffix:
        return cell_class(name, pins.prefix)
    return cell_class(name, pins.prefix, pins.policy, pins.suffix)


# ------------------------------------------------------------------------------------------------ netlist
class Gate:
    __slots__ = ("kind", "inst", "pins")

    def __init__(self, kind, inst, pins):
        self.kind, self.inst, self.pins = kind, inst, pins


class Netlist:
    def __init__(self):
        self.name = None
        self.ports = []        # (name, dir, width)
        self.gates = []
        self.alias = {}        # net -> net (from `assign`)
        self.pi = []           # primary input bits
        self.po = []           # (port, bit, net)
        self.ranges = {}       # vector port -> (hi, lo) as declared
        self.aux = set()       # instances that are not gates of the scored netlist (a 2-cell build's helper, a Q inverter)

    def port_bit(self, port, k):
        """The Verilog name of bit `k` (counted from the LSB, as `po` counts) of `port`: `y[3]`, or `z` for a scalar port."""
        r = self.ranges.get(port)
        return f"{port}[{r[1] + k}]" if r else port

    def resolve(self, net):
        seen = 0
        while net in self.alias:
            net = self.alias[net]
            seen += 1
            if seen > 100000:
                raise PpaError("netlist: alias loop")
        return net


def _split_top(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


_CONST_RE = re.compile(r"(\d+)'s?([bBoOdDhH])([0-9a-fA-FxXzZ_?]+)")


# A net reference: an escaped identifier (`\name`, every non-space character after the backslash, ended by the
# whitespace Yosys always prints after it, and possibly containing `[`, `]` and `.`) or a plain one, then an optional
# bit or part select, with optional whitespace before the `[` (`\_8_.B [23:8]`).
_REF_RE = re.compile(r"(\\\S+|[^\s\[\]]+)(?:\s*\[(\d+)(?::(\d+))?\])?")


XBIT = "1'bx"     # the net an x/z constant bit becomes on the right of an `assign`: not a Verilog identifier, so no clash


def _bits(expr, widths, xok=False):
    """A Verilog net expression -> list of bit nets, MSB first. `widths`: declared vector name -> (hi, lo); the bit
    nets of a vector are named `name[i]`, i = hi down to lo. An x/z constant is an error on a cell pin; on the right of
    an `assign` (`xok`) every bit of it becomes the net XBIT instead, because Yosys leaves such constants in the dead
    public-named wires of expanded cells (`assign {\\_8_.buffer [63:32], ...} = { 32'hxxxxxxxx, y };`), and the weighing
    refuses only if a gate or an output actually reads one (Design)."""
    expr = expr.strip()
    if expr.startswith("{") and expr.endswith("}"):
        out = []
        for part in _split_top(expr[1:-1]):
            out += _bits(part, widths, xok)
        return out
    m = _CONST_RE.fullmatch(expr)
    if m:
        w, base, digits = int(m.group(1)), m.group(2).lower(), m.group(3)
        if re.search(r"[xXzZ?]", digits):
            if xok:
                return [XBIT] * w
            raise PpaError(f"netlist: constant {expr} has x/z bits; a 2-state weighing is undefined")
        v = int(digits.replace("_", ""), {"b": 2, "o": 8, "d": 10, "h": 16}[base])
        return [str((v >> i) & 1) for i in reversed(range(w))]
    m = _REF_RE.fullmatch(expr)
    if m is None:
        return [expr]
    name, hi, lo = m.group(1), m.group(2), m.group(3)
    if hi is not None and lo is None:
        return [f"{name}[{int(hi)}]"]
    if hi is not None:
        return [f"{name}[{i}]" for i in range(int(hi), int(lo) - 1, -1)]
    rng = widths.get(name)
    if rng is None:
        return [name]
    return [f"{name}[{i}]" for i in range(rng[0], rng[1] - 1, -1)]


_INST_RE = re.compile(r"^\s*(\\?\$?[\w$]+)\s+(\\?\S+)\s*\(\s*((?:\.\w+\([^)]*\)\s*,?\s*)+)\)\s*;", re.M)
_INST_OPEN_RE = re.compile(r"^\s*(?!module\b|input\b|output\b|inout\b|wire\b|reg\b|assign\b)\\?\$?[\w$]+\s+\\?\S+\s*\(\s*\.", re.M)
_PIN_RE = re.compile(r"\.(\w+)\(([^)]*)\)")


def parse_netlist(text):
    """The structural Verilog `write_verilog -noattr -noexpr` emits: `\\$_AND_ _12_ (.A(x), .B(y), .Y(z));` instances,
    port vectors, `assign` of nets. One flat module, no behavioral code."""
    nl = Netlist()
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    mods = re.findall(r"^\s*module\s+(\S+?)\s*\(", text, re.M)
    if len(mods) != 1:
        raise PpaError(f"netlist: expected one flat module, found {len(mods)}")
    nl.name = mods[0]
    widths = {}
    # `(\S+)\s*;`: Yosys writes an escaped port name with a space before the semicolon (`input \\a[0] ;`); a port line
    # this regex cannot read is refused below, never skipped (a skipped port would leave its load unweighed)
    port_re = r"^\s*(input|output|inout)\s*(?:\[(\d+):(\d+)\])?\s*(\S+)\s*;"
    declared = re.findall(r"^\s*(?:input|output|inout)\b[^;]*;", text, re.M)
    parsed = list(re.finditer(port_re, text, re.M))
    if len(parsed) != len(declared):
        unread = [d.strip() for d in declared if not re.match(port_re, d)]
        raise PpaError(f"netlist: unreadable port declaration(s): {unread[:3]!r}")
    for d in parsed:
        if d.group(1) == "inout":
            raise PpaError(f"netlist: inout port {d.group(4)}")
        w = 1 if d.group(2) is None else int(d.group(2)) - int(d.group(3)) + 1
        nl.ports.append((d.group(4), d.group(1), w))
        if d.group(2) is not None:
            widths[d.group(4)] = nl.ranges[d.group(4)] = (int(d.group(2)), int(d.group(3)))
    # wires, including the public-named (often escaped) ones Yosys leaves of the cells a techmap expanded: `wire [7:0] \_1_.A ;`
    for d in re.finditer(r"^\s*wire\s*\[(\d+):(\d+)\]\s*(\\\S+|[^\s;]+)\s*;", text, re.M):
        widths.setdefault(d.group(3), (int(d.group(1)), int(d.group(2))))
    for name, direction, w in nl.ports:
        if direction == "input":
            nl.pi += reversed(_bits(name, widths))     # LSB first, as always
    for a in re.finditer(r"^\s*assign\s+(.+?)\s*=\s*(.+?);", text, re.M | re.S):
        lhs, rhs = _bits(a.group(1), widths), _bits(a.group(2), widths, xok=True)
        if len(lhs) != len(rhs):
            raise PpaError(f"netlist: assign width mismatch: {a.group(0)[:80]!r}")
        for l, r in zip(lhs, rhs):
            nl.alias[l] = r
    for g in _INST_RE.finditer(text):
        kind = g.group(1).lstrip("\\")
        if kind in ("module", "input", "output", "inout", "wire", "reg", "assign"):
            continue
        pins = {}
        for p in _PIN_RE.finditer(g.group(3)):
            bits = _bits(p.group(2), widths)
            if len(bits) != 1:
                raise PpaError(f"netlist: pin {p.group(0)} of {kind} is not one bit")
            if p.group(1) in pins:
                raise PpaError(f"netlist: pin {p.group(1)} of {kind} {g.group(2)} connected twice")
            pins[p.group(1)] = bits[0]
        nl.gates.append(Gate(kind, g.group(2), pins))
    if len(_INST_OPEN_RE.findall(text)) != len(nl.gates):
        raise PpaError("netlist: some instances could not be read (the reader understands `TYPE name (.PIN(net), ...);`)")
    for name, direction, w in nl.ports:
        if direction == "output":
            for i, net in enumerate(reversed(_bits(name, widths))):
                nl.po.append((name, i, net))
    return nl


# ------------------------------------------------------------------------------------------------ flow A0'
def expand_a0(nl, pins):
    """The scored netlist (Yosys `$_X_` gates) as sky130 cell instances, one cell per gate. Raises PpaError on a gate
    kind outside the abc -g flow's inventory (a flip-flop, a latch, a tri-state, a cell of another library ...)."""
    out = Netlist()
    out.name, out.ports, out.alias, out.pi, out.po, out.ranges = nl.name, nl.ports, nl.alias, nl.pi, nl.po, nl.ranges
    bad = defaultdict(int)
    for g in nl.gates:
        m = re.fullmatch(r"\$_(\w+?)_", g.kind)
        if not (m and m.group(1) in pins.gates):
            bad[g.kind] += 1
    if bad:
        raise PpaError(f"the netlist has cells outside the A0' table (only the gates of `abc -g` are weighed): "
                       f"{dict(sorted(bad.items()))}")
    fresh = Fresh(nl, "svgm")
    for g in nl.gates:
        gate = re.fullmatch(r"\$_(\w+?)_", g.kind).group(1)
        want = set(GATE_SEMANTICS[gate][0]) | {"Y"}
        if set(g.pins) != want:
            raise PpaError(f"gate {g.inst} ({g.kind}) has pins {sorted(g.pins)}, expected {sorted(want)}")
        cells = pins.gate_cells[gate]
        sig = {p: n for p, n in g.pins.items()}
        for k, (cname, conn, op, osig) in enumerate(cells):
            last = k == len(cells) - 1
            # the cell that drives Y keeps the gate's instance name; a cell before it (a 2-cell build) is a helper, whose
            # instance and output net get fresh names and which the unit depth does not count (`Netlist.aux`)
            inst = g.inst if last else fresh.name()
            if not last:
                sig[osig] = inst + "_n"
                out.aux.add(inst)
            cp = {p: sig[s] for p, s in conn.items()}
            cp[op] = sig[osig]
            out.gates.append(Gate(pins.full(cname), inst, cp))
    return out


class Fresh:
    """Fresh instance names `<prefix><k>` (their nets `<prefix><k>_n`) that no net, instance or port of `nl` starts with
    (the prefix grows by `_` until none does)."""

    def __init__(self, nl, prefix, extra=()):
        names = set(nl.pi) | {g.inst for g in nl.gates} | {n for g in nl.gates for n in g.pins.values() if n} \
            | set(nl.alias) | set(nl.alias.values()) | {p for p, _, _ in nl.ports} | {n for _, _, n in nl.po} | set(extra)
        while any(x.lstrip("\\").startswith(prefix) for x in names):
            prefix += "_"
        self.prefix, self.k = prefix, 0

    def name(self):
        self.k += 1
        return f"{self.prefix}{self.k - 1}"


def invert_flop_q(nl, flops, pins):
    """A library flop with only an inverted output (asap7's DFFHQNx1: QN = !D of the last clock edge) as the clocked flow's
    $_DFF_P_: each flop's output becomes a fresh net (the cell's QN) and the pins' `q_inverter` (an inverter of the
    library, a real cell weighed like any other, its input that net) drives the scored netlist's Q net. The flops with their
    Q pins moved; the inverters are appended to `nl.gates` and are helpers (`Netlist.aux`: the unit depth counts the
    scored netlist's gates only). No change when the library's flop has Q."""
    inv = pins.flop["q_inverter"]
    if not inv or not flops:
        return flops
    fresh = Fresh(nl, "svgq", [x for f in flops for x in f.pins.values()] + [f.inst for f in flops])
    out = []
    for f in flops:
        inst = fresh.name()
        qn = inst + "_n"
        nl.gates.append(Gate(pins.full(inv["cell"]), inst, {inv["in"]: qn, inv["out"]: f.pins["Q"]}))
        nl.aux.add(inst)
        out.append(Gate(f.kind, f.inst, {**f.pins, "Q": qn}))
    return out


# ------------------------------------------------------------------------------------------------ design and STA
class Audit:
    """The electrical legality of one weighing (sky130_a0_v2): every table read outside its grid, every driver over its
    pin's max_capacitance, every net whose transition exceeds the max_transition of its driver or of a pin it reaches.
    Entries are (ratio, text); the ratio is how far over the limit (load / max_capacitance, transition / max_transition,
    for a table the factor by which the read point lies past the grid's nearer bound, in the worse of its two dimensions).
    Table reads are counted one by one and reported per cell (its worst read). A net whose tables were left has no known
    transition (nothing is extrapolated): its transition violations, if any, are hidden behind its table violation."""

    def __init__(self, floor=False):
        self.cap, self.trans = [], []
        self.table, self.table_reads = {}, 0           # (cell, instance, net) -> (worst ratio, text); every read counted
        # the pins' timing.below_grid = "floor" (asap7): a read below a grid in a dimension, and not above it in the other,
        # is read at the grid's floor and only counted (`floored`); "reject" (sky130): it is a violation like any other
        self.floor, self.floored = floor, 0
        self.worst_load = self.worst_trans = 0.0       # the largest ratios seen, violations or not (the headroom)
        # net -> the kinds of violation it is the cause of, for the repair (`repair`): "cap" (load over max_capacitance),
        # "load" (a table read past the grid's largest load), "trans" (transition over max_transition, or past the largest
        # transition a constraint table of the pin it reaches is characterized for), "low" (a read BELOW a grid: a transition
        # or a load smaller than the library characterizes, which no buffer can fix). A read past the largest INPUT
        # transition is not the read's own net's fault but its input's, which carries "trans" (or, its own transition being
        # unknown, the violation of its driver) itself.
        self.blame = defaultdict(set)

    def out_of_table(self, where, tbl, x1, x2):
        inst, net, cell = where

        def beyond(x, lo, hi):          # the factor by which x lies past the nearer bound (1.0 inside)
            if x > hi:
                return x / hi
            if x < lo:
                return lo / x if x > 0 else float("inf")
            return 1.0
        if self.floor:          # below a grid is read at its floor: only the dimension past the top is a violation
            x1, x2 = max(x1, tbl.i1[0]), max(x2, tbl.i2[0])
        r = max(beyond(x1, tbl.i1[0], tbl.i1[-1]), beyond(x2, tbl.i2[0], tbl.i2[-1]))
        if x1 < tbl.i1[0] or x2 < tbl.i2[0]:
            self.blame[net].add("low")
        elif x2 > tbl.i2[-1]:
            # a setup table's second index is the D net's transition; every other table's is the net's load
            self.blame[net].add("trans" if inst == "D" else "load")
        self.table_reads += 1
        key = (cell, inst, net)
        if key not in self.table or r > self.table[key][0]:
            self.table[key] = (r, f"{_short(cell)} {inst} driving net {net}: input transition {x1 * 1000:.0f} ps, load "
                                  f"{x2 * 1000:.1f} fF, table grid {tbl.i1[0] * 1000:g} to {tbl.i1[-1] * 1000:g} ps x "
                                  f"{tbl.i2[0] * 1000:g} to {tbl.i2[-1] * 1000:g} fF")

    def violations(self):
        return len(self.table) + len(self.cap) + len(self.trans)

    def report(self, top=3):
        """One paragraph naming the worst cells of each kind with their ratios (the rejection's message)."""
        parts = []
        for what, rows in (("drivers over max_capacitance", self.cap), ("nets over max_transition", self.trans),
                           (f"cells read outside their timing tables ({self.table_reads} reads)", list(self.table.values()))):
            if rows:
                worst = sorted(rows, key=lambda r: (-r[0], r[1]))[:top]
                parts.append(f"{len(rows)} {what}, worst: " + "; ".join(f"{t} ({r:.2f}x)" for r, t in worst))
        return ". ".join(parts)

    def summary(self):
        out = {"worst_load_ratio": round(self.worst_load, 3), "worst_transition_ratio": round(self.worst_trans, 3),
               "over_max_capacitance": len(self.cap), "over_max_transition": len(self.trans),
               "cells_outside_tables": len(self.table), "table_reads_outside": self.table_reads}
        if self.floor:
            out["table_reads_floored"] = self.floored
        return out


def new_audit(pins):
    """An Audit under the pins' below-grid rule (timing.below_grid)."""
    return Audit(floor=pins.below_grid == "floor")


def _short(cell):
    return cell.split("__", 1)[1] if "__" in cell else cell


A1_EXTRAPOLATES = "flow A1' (sky130_a1_v1): linear extrapolation outside the grid, unchanged"   # a sentinel `audit`


def _read(tbl, x1, x2, audit, where):
    """`tbl.at(x1, x2)`; with an Audit, a point outside the grid is recorded and read at the clamped point instead (the
    weighing will reject, so that value is never reported). `audit` = A1_EXTRAPOLATES: flow A1''s reading, kept as it was
    (the 2026-11-04 decision changed the ranked flow only; A1' is an unranked research column): bilinear inside the grid, linear
    extrapolation outside it. Only `analyze_cells` passes it; the ranked weighing (`analyze`) always passes an Audit."""
    if audit is A1_EXTRAPOLATES:
        return tbl._bilinear(x1, x2)
    if audit is None or tbl.covers(x1, x2):
        return tbl.at(x1, x2)
    if audit.floor and x1 <= tbl.i1[-1] and x2 <= tbl.i2[-1]:
        # below the grid only (timing.below_grid = "floor"): read at the floor (asap7's delay tables rise from their first
        # point along both axes, so the floor errs slow: MEASURED, test_ppa_asap7.py), counted, not a violation
        audit.floored += 1
        return tbl.at(*tbl.clamp(x1, x2))
    audit.out_of_table(where, tbl, x1, x2)
    return tbl.at(*tbl.clamp(x1, x2))


def drive_arrival(cell, slew_ns, load, audit, where):
    """{edge: (arrival, transition)} of the output of the one-input driving `cell` whose input is an ideal ramp of `slew_ns`
    at 0, at output load `load` (pF; or {edge: pF}, each output edge at its own load: `Design.load_edge_pf`). The ramp has
    both edges, so each output edge is the arc's own table. The arrival is the cell's WHOLE delay, as if the cell were an
    instance of the netlist: OpenSTA timing the same netlist with one explicit instance of the drive per input agrees to
    1 fs (MEASURED 2026-11-04 for buf_1, score/test_ppa_opensta.py). OpenSTA's `set_driving_cell` is another model: it adds only
    the load-dependent part, delay(load) - delay(0) with the zero-load delay extrapolated, so it is earlier by that
    zero-load delay (buf_1 at the 50 ps ramp: 58.7 ps on a rising input, 72.8 ps on a falling one; buf_8 74.6 and 106.2 ps
    by the same extrapolation of its tables)."""
    if len(cell.inputs) != 1 or len(cell.outputs) != 1 or len(cell.arcs[cell.outputs[0]]) != 1:
        raise PpaError(f"the driving cell {cell.name} is not a one-input, one-output, one-arc cell")
    arc = cell.arcs[cell.outputs[0]][0]
    loads = load if isinstance(load, dict) else {"r": load, "f": load}
    return {e: (_read(arc.tbl["cell_" + w], slew_ns, loads[e], audit, where),
                _read(arc.tbl[w + "_transition"], slew_ns, loads[e], audit, where))
            for e, w in (("r", "rise"), ("f", "fall"))}


class Design:
    """The gate graph over liberty cells, checked: every read net is a primary input, a constant or driven exactly
    once; no combinational loop; every cell a logic-class cell with exactly its pins connected."""

    def __init__(self, nl, lib, pins):
        self.nl, self.lib = nl, lib
        self.aux = set(getattr(nl, "aux", ()))     # helper cells: not counted by the unit depth
        self.cells, self.ins, self.outs, self.names = [], [], [], []
        self.driver = {}
        pi = set(nl.pi)
        if len(pi) != len(nl.pi):
            raise PpaError("netlist: duplicate primary-input bits")
        for g in nl.gates:
            cls = pins_class(g.kind, pins)
            if cls != "logic":
                raise PpaError(f"cell {g.kind} (instance {g.inst}) is of class {cls!r}, not an ordinary combinational cell")
            c = lib.cell(g.kind)
            unknown = [p for p in g.pins if p not in c.inputs and p not in c.outputs]
            floating = [p for p in c.inputs if p not in g.pins]
            if unknown or floating:
                raise PpaError(f"instance {g.inst} of {g.kind}: unknown pins {unknown}, unconnected inputs {floating}")
            ins = {p: nl.resolve(n) for p, n in g.pins.items() if p in c.inputs}
            outs = {p: n for p, n in g.pins.items() if p in c.outputs}
            idx = len(self.cells)
            self.cells.append(c)
            self.ins.append(ins)
            self.outs.append(outs)
            self.names.append(g.inst)
            for p, n in outs.items():
                if n in self.driver:
                    raise PpaError(f"net {n} is driven by two cells ({self.names[self.driver[n][0]]} and {g.inst})")
                if n in pi or n in nl.alias or n in ("0", "1"):
                    raise PpaError(f"net {n}, driven by {g.inst}, is also a primary input, a constant or an assign target")
                self.driver[n] = (idx, p)
        self.fanout = defaultdict(list)
        for i, ins in enumerate(self.ins):
            for p, n in ins.items():
                self.fanout[n].append((i, p))
        self.po_count = defaultdict(int)
        self.po_nets = []
        for _, _, net in nl.po:
            r = nl.resolve(net)
            self.po_nets.append(r)
            self.po_count[r] += 1
        if not self.po_nets:
            raise PpaError("netlist: no output bits")
        for n in list(self.fanout) + self.po_nets:
            if n == XBIT:
                raise PpaError("netlist: a cell input or an output bit is an x/z constant; a 2-state weighing is undefined")
            if n not in ("0", "1") and n not in self.driver and n not in pi:
                raise PpaError(f"net {n} is read but never driven (not an input, a constant or a cell output)")
        self.uses_constant = any(n in ("0", "1") for n in list(self.fanout) + self.po_nets)
        self.extra_load = defaultdict(float)     # pin loads outside the gate graph (flop D pins)
        self.extra_load_e = {"r": defaultdict(float), "f": defaultdict(float)}      # the same per edge
        self.order = self._topo()

    def _topo(self):
        indeg = [0] * len(self.cells)
        succ = defaultdict(list)
        for i, ins in enumerate(self.ins):
            seen = []
            for n in ins.values():
                if n in self.driver and n not in seen:
                    seen.append(n)
                    succ[self.driver[n][0]].append(i)
                    indeg[i] += 1
        ready = [i for i in range(len(self.cells)) if indeg[i] == 0]
        order = []
        while ready:
            i = ready.pop()
            order.append(i)
            for k in succ[i]:
                indeg[k] -= 1
                if indeg[k] == 0:
                    ready.append(k)
        if len(order) != len(self.cells):
            raise PpaError("netlist: combinational loop")
        return order

    def load_pf(self, net, po_load_pf):
        """The net's load at the pins' `capacitance` (the energy model's C; timing reads `load_edge_pf`)."""
        c = sum(self.cells[i].pin_cap[p] for i, p in self.fanout.get(net, ()))
        return c + po_load_pf * self.po_count.get(net, 0) + self.extra_load.get(net, 0.0)

    def load_edge_pf(self, net, po_load_pf, e):
        """The load a transition `e` ("r"/"f") of the net sees: every pin's rise_capacitance or fall_capacitance (what timing
        reads, as OpenSTA does: `edge_caps`), po_load per output bit, the flop D pins' per edge."""
        c = sum(self.cells[i].pin_cap_e[p][e] for i, p in self.fanout.get(net, ()))
        return c + po_load_pf * self.po_count.get(net, 0) + self.extra_load_e[e].get(net, 0.0)

    def load_max_pf(self, net, po_load_pf):
        """The larger edge's load: what max_capacitance is checked against (OpenSTA checks each edge)."""
        return max(self.load_edge_pf(net, po_load_pf, e) for e in "rf")

    def sta(self, pi_slew_ns, po_load_pf, starts=None, ends=(), drive=None, audit=None):
        """Graph-based NLDM STA. Arrival and transition per (net, rising/falling); for each cell output edge every
        timing arc of every related pin is evaluated by bilinear interpolation at (input transition, output load), the
        unateness picks the input edge, the worst arrival wins and the largest transition is carried (OpenSTA's
        graph-based convention). load = the fan-out pins' rise_capacitance (a rising output edge) or fall_capacitance (a
        falling one) + po_load per primary-output bit; no wires. With those loads, on ideal ramps or behind an explicit input
        buffer, it equals OpenSTA (openroad/orfs 26Q4) to 1 fs per arc on every cell with a function and on the references
        (MEASURED 2026-11-04; test_ppa_opensta.py).
        Returns (T in ns, critical path [(net, edge, arrival ns)]). Constants and constant-fed cones have no arrival.
        A clocked netlist (`weigh_cells`) passes `starts` {net: {edge: (arrival, transition)}} for the flop Q nets
        (clock-to-Q at the ideal clock edge) and `ends` [(net, setup)] for the flop D nets, `setup(edge, transition)` in
        ns: T is then the register-to-register period, the latest of every output arrival and every D arrival + setup.
        Primary inputs: with `drive` (a Cell, sky130_a0_v3: the task's `input_drive_cell`) every primary input that is read
        is the output of that cell, whose input is an ideal ramp of `pi_slew_ns` arriving at 0, at the input net's real
        load per edge, the cell's whole delay counted (as an instance of the netlist would be, not OpenSTA's
        set_driving_cell: `drive_arrival`); without it (flow A1') an ideal ramp of `pi_slew_ns` at 0, whatever the load.
        Every table read is inside the table's grid: with an `audit` a read outside it is recorded there (and the run
        continues on the clamped point, so that the audit is complete; the caller must then reject, never report),
        without one it raises TableRange. `self.arr` keeps the arrivals and transitions of the last run."""
        arr = {}
        for n in self.nl.pi:
            st = (starts or {}).get(n)
            if st is None and drive is not None:
                if self.load_pf(n, po_load_pf) <= 0.0:              # read by nothing: no arrival is ever needed
                    continue
                st = drive_arrival(drive, pi_slew_ns, {e: self.load_edge_pf(n, po_load_pf, e) for e in "rf"}, audit,
                                   ("(input driver)", n, drive.name))
            for e in "rf":
                t, s = (st or {}).get(e, (0.0, pi_slew_ns))
                arr[(n, e)] = (t, s, None)
        for i in self.order:
            c = self.cells[i]
            for op, onet in self.outs[i].items():
                where = (self.names[i], onet, c.name)
                for e in "rf":
                    load = self.load_edge_pf(onet, po_load_pf, e)
                    best = None
                    smax = 0.0
                    for arc in c.arcs[op]:
                        inet = self.ins[i].get(arc.related)
                        if inet is None or inet in ("0", "1"):
                            continue
                        if arc.sense == "positive_unate":
                            ies = (e,)
                        elif arc.sense == "negative_unate":
                            ies = ("f" if e == "r" else "r",)
                        else:
                            ies = ("r", "f")
                        for ie in ies:
                            a = arr.get((inet, ie))
                            if a is None:
                                continue
                            t0, s0, _ = a
                            dkey = "cell_rise" if e == "r" else "cell_fall"
                            tkey = "rise_transition" if e == "r" else "fall_transition"
                            d = _read(arc.tbl[dkey], s0, load, audit, where)
                            smax = max(smax, _read(arc.tbl[tkey], s0, load, audit, where))
                            if best is None or t0 + d > best[0]:
                                best = (t0 + d, (inet, ie))
                    if best is not None:
                        arr[(onet, e)] = (best[0], smax, best[1])
        self.arr = arr
        worst = None
        for n, setup in [(n, None) for n in self.po_nets] + list(ends):
            for e in "rf":
                a = arr.get((n, e))
                t = a and a[0] + (setup(e, a[1]) if setup else 0.0)
                if a and (worst is None or t > worst[0]):
                    worst = (t, (n, e))
        path = []
        if worst:
            cur = worst[1]
            while cur is not None:
                path.append((cur[0], cur[1], arr[cur][0]))
                cur = arr[cur][2]
            path.reverse()
        return (worst[0] if worst else 0.0), path

    def sinks_text(self, net, d_pins=0):
        """What a net drives, in the words of the design: '24 output bits (y[0] .. y[23]), 3 cell pins, 2 flop D pins'."""
        bits = [self.nl.port_bit(p, b) for p, b, n in self.nl.po if self.nl.resolve(n) == net]
        parts = []
        if bits:
            parts.append(f"{len(bits)} output bit{'s' if len(bits) > 1 else ''} ("
                         + (bits[0] if len(bits) == 1 else f"{bits[0]} .. {bits[-1]}" if len(bits) > 2 else
                            f"{bits[0]}, {bits[1]}") + ")")
        k = len(self.fanout.get(net, ()))
        if k:
            parts.append(f"{k} cell pin{'s' if k > 1 else ''}")
        if d_pins:
            parts.append(f"{d_pins} flop D pin{'s' if d_pins > 1 else ''}")
        return ", ".join(parts) or "nothing"

    def legality(self, po_load_pf, audit, default_trans, sources=(), sink_trans=None, ties=()):
        """After `sta`: every driven net against its driver's limits. A cell output: the load (the larger edge's,
        `load_max_pf`) against the output pin's max_capacitance; the larger edge transition (where the net has an arrival) against the output pin's max_transition and
        that of every pin it reaches (the library's default_max_transition where a pin declares none). `sources`: the drivers
        outside the gate graph, [(net, cell, label, max_capacitance, max_transition)] (the driving cell of the primary inputs,
        the flops' Q); `sink_trans`: {net: [max_transition of a pin outside the gate graph]} (the flops' D); `ties`: the tie
        cells' outputs, [(instance, cell, pin, net label, load, max_capacitance, sinks text)] (no timing arcs: the load
        only).
        Every violation is also recorded in `audit.blame` under its net."""
        sink_trans = sink_trans or {}
        unknown = {net for _, _, net in audit.table}      # its driver's tables were left: its transition is not known

        def check(net, cell, label, mc, mt):
            edges = [self.arr[(net, e)][1] for e in "rf" if (net, e) in self.arr]
            load = self.load_max_pf(net, po_load_pf)
            if load <= 0.0 and not edges:
                return

            def what():
                return f"{_short(cell)} {label} driving net {net} ({self.sinks_text(net, len(sink_trans.get(net, ())))}"
            if mc:
                r = load / mc
                audit.worst_load = max(audit.worst_load, r)
                if r > 1.0:
                    audit.cap.append((r, f"{what()}): load {load * 1000:.1f} fF, max_capacitance {mc * 1000:.1f} fF"))
                    audit.blame[net].add("cap")
            limits = [mt or default_trans] + [self.cells[i].max_trans.get(p, default_trans)
                                              for i, p in self.fanout.get(net, ())] + list(sink_trans.get(net, ()))
            limits = [x for x in limits if x]
            if edges and limits and net not in unknown:
                slew, lim = max(edges), min(limits)
                r = slew / lim
                audit.worst_trans = max(audit.worst_trans, r)
                if r > 1.0:
                    audit.trans.append((r, f"{what()}): transition {slew * 1000:.0f} ps, max_transition "
                                           f"{lim * 1000:.0f} ps"))
                    audit.blame[net].add("trans")
        for net, cell, label, mc, mt in sources:
            check(net, cell, label, mc, mt)
        for i in self.order:
            c = self.cells[i]
            for op, onet in self.outs[i].items():
                check(onet, c.name, self.names[i], c.max_cap.get(op), c.max_trans.get(op))
        for inst, _, pin, label, load, mc, sinks in ties:
            r = load / mc
            audit.worst_load = max(audit.worst_load, r)
            if r > 1.0:
                audit.cap.append((r, f"tie cell {inst} {pin} driving constant {label} ({sinks}): load {load * 1000:.1f} fF, "
                                     f"max_capacitance {mc * 1000:.1f} fF"))
                audit.blame[label].add("cap")

    def unit_depth(self, ends=()):
        """Gates on the longest path, counting the scored netlist's gates only (a helper cell, `Netlist.aux`, counts 0: a
        2-cell build of one gate is one level, a flop's Q inverter none)."""
        lv = {}
        for i in self.order:
            l = (0 if self.names[i] in self.aux else 1) + max([lv.get(n, 0) for n in self.ins[i].values()] or [0])
            for onet in self.outs[i].values():
                lv[onet] = l
        return max(lv.get(n, 0) for n in self.po_nets + [n for n, _ in ends])


class Analysis:
    """Everything measured on one netlist (floats are the STA's, unrounded)."""

    def __init__(self):
        self.t_ns = 0.0
        self.area_e4 = 0
        self.cells = 0
        self.hist = {}
        self.unit_depth = 0
        self.constants = False
        self.path = []
        self.crit_output = None
        self.crit_edge = None
        self.flops = None          # the flop count of a clocked netlist (None: combinational)
        self.scored_gates = None   # the scored netlist's gates (+ flops): what score.py counts
        self.repair = None         # the repair's record (the ranked flow)
        self.audit = None          # the legality audit (the ranked flow)
        self.design = None         # the weighed Design, after its STA (`design.arr`: arrivals and transitions)
        self.flop_gates, self.q, self.dn, self.inputs = [], [], [], []   # the ranked flow's flops, Q / D nets, input bits
        self.input_drive = None    # the cell driving every primary input (the ranked flow, `input_drive_of`)


# ------------------------------------------------------------------------------------------------ clocked netlists
FLOP_KIND, FLOP_CELL = "$_DFF_P_", "dfxtp_1"     # the clocked flow's one flop (score/svgolf_seq.ys) and its sky130 cell


class FlopTiming:
    """dfxtp_1 from the liberty: area, D pin capacitance, the CLK->Q rising_edge arc, the setup_rising constraint, and the
    limits of its Q (max_capacitance, max_transition) and D (max_transition) pins."""

    def __init__(self, lib, pins):
        fp = pins.flop
        name = pins.full(fp["cell"])
        if not lib.has(name):
            raise PpaError(f"the liberty has no {name}, the cell of the clocked flow's $_DFF_P_")
        g = lib.group(name)
        tdiv, cdiv = lib.tdiv, lib.cdiv
        templates = lib.templates_of(name)
        self.name = name
        self.area_e4 = _area_e4(g.attrs.get("area"), name, lib.decimals)
        self.cq = self.setup = None
        self.q_max_cap = self.q_max_trans = self.d_max_trans = None
        self.q_pin, self.d_pin, self.clock_pin = fp["q"], fp["d"], fp["clock"]
        for p in g.find("pin"):
            if p.args[0] == fp["d"]:
                self.d_cap = _num(p.attrs["capacitance"], cdiv)
                self.d_cap_e = edge_caps(p, cdiv)
                self.d_max_trans = _num(p.attrs["max_transition"], tdiv) if "max_transition" in p.attrs else None
            if p.args[0] == fp["q"]:
                self.q_max_cap = _num(p.attrs["max_capacitance"], cdiv) if "max_capacitance" in p.attrs else None
                self.q_max_trans = _num(p.attrs["max_transition"], tdiv) if "max_transition" in p.attrs else None
                self.q_function = p.attrs.get("function")
            for t in p.find("timing"):
                tt = t.attrs.get("timing_type")
                if p.args[0] == fp["q"] and tt == "rising_edge" and t.attrs.get("related_pin") == fp["clock"]:
                    self.cq = delay_tables(t, f"{name} {fp['clock']}->{fp['q']}", templates, tdiv, cdiv)
                elif p.args[0] == fp["d"] and tt == "setup_rising":
                    self.setup = {k: _constraint_table(t, k, templates, tdiv, f"{name} setup {k}")
                                  for k in ("rise_constraint", "fall_constraint")}
        if self.cq is None or self.setup is None:
            raise PpaError(f"liberty: {name} has no rising_edge {fp['clock']}->{fp['q']} arc or no setup_rising constraint")
        self._check_function(g, lib, pins)

    def _check_function(self, g, lib, pins):
        """The cell is a positive-edge flop on the pins' clock whose output is D of the last edge (no `q_inverter`) or its
        complement (a `q_inverter` forms Q, which must then be an inverter of the library): from its `ff` group, read as the
        liberty states it (the state variable takes next_state at clocked_on; the output's function names the state
        variable, its complement variable, or the negation of one of them)."""
        ffs = g.find("ff")
        fp = pins.flop
        if len(ffs) != 1 or len(ffs[0].args) != 2:
            raise PpaError(f"liberty: {self.name} has no single ff group")
        var, nvar = ffs[0].args
        clk = re.sub(r"[\s()\"]", "", ffs[0].attrs.get("clocked_on") or "")
        ns = re.sub(r"[\s()\"]", "", ffs[0].attrs.get("next_state") or "")
        fn = re.sub(r"[\s()\"]", "", self.q_function or "")
        pol = {fp["d"]: 1, "!" + fp["d"]: -1}.get(ns)
        out = {var: 1, nvar: -1, "!" + var: -1, "!" + nvar: 1}.get(fn)
        if clk != fp["clock"] or pol is None or out is None:
            raise PpaError(f"liberty: {self.name} is not a positive-edge flop of {fp['clock']} and {fp['d']} "
                           f"(clocked_on {clk!r}, next_state {ns!r}, {fp['q']} = {fn!r})")
        inverted = pol * out < 0
        if inverted != bool(fp["q_inverter"]):
            raise PpaError(f"liberty: {self.name} {fp['q']} = {'!' if inverted else ''}D of the last clock edge, and the "
                           "pins " + ("form no Q from it (flop.q_inverter)" if inverted else "invert it (flop.q_inverter)"))
        if inverted:
            inv = fp["q_inverter"]
            c = lib.cell(pins.full(inv["cell"]))
            fn = re.sub(r"[\s()]", "", c.function.get(inv["out"]) or "")
            if (c.inputs != [inv["in"]] or c.outputs != [inv["out"]] or fn != "!" + inv["in"]
                    or pins_class(c.name, pins) != "logic"):
                raise PpaError(f"pins: flop.q_inverter {inv['cell']} is not a one-input logic inverter {inv['in']} -> "
                               f"{inv['out']} of the liberty")


def _constraint_table(t, k, templates, tdiv, what):
    """The setup table `k` of timing group `t` as a Table whose first index is the clock's transition and whose second is
    the constrained (D) pin's, whichever way the liberty stores it (sky130: related_pin_transition first; asap7:
    constrained_pin_transition first, transposed here)."""
    found = t.find(k)
    if len(found) != 1:
        raise PpaError(f"liberty: {what}: expected one {k} table, found {len(found)}")
    tg = found[0]
    tpl = templates.get(tg.args[0] if tg.args else None)
    if tpl == ("related_pin_transition", "constrained_pin_transition"):
        return Table(tg, what, tdiv, tdiv, tdiv)
    if tpl == ("constrained_pin_transition", "related_pin_transition"):
        return Table(tg, what, tdiv, tdiv, tdiv, transpose=True)
    raise PpaError(f"liberty: {what}: template {tg.args} has variables {tpl}, not the clock's and the D pin's transitions")


class _FlopArc:
    __slots__ = ("related", "sense", "tbl")

    def __init__(self, tbl, related="CLK"):
        self.related, self.sense, self.tbl = related, "non_unate", tbl


class FlopDrive:
    """The Q of a dfxtp_1 as the primary inputs' driving cell (input_drive sky130_fd_sc_hd__dfxtp_1), shaped like a
    one-input, one-output, one-arc Cell for `drive_arrival`, `Budgets.pi` and the legality audit: its one arc is the CLK->Q
    rising_edge arc, read at (the ideal clock's transition = pi_slew, the input net's load), both output edges from the one
    clock edge at 0, exactly as `weigh_cells` starts a flop's Q net inside a clocked design; its limits are the Q pin's."""

    def __init__(self, ft):
        self.name = ft.name
        self.inputs, self.outputs = [ft.clock_pin], [ft.q_pin]
        self.arcs = {ft.q_pin: [_FlopArc(ft.cq, ft.clock_pin)]}
        self.max_cap = {ft.q_pin: ft.q_max_cap} if ft.q_max_cap else {}
        self.max_trans = {ft.q_pin: ft.q_max_trans} if ft.q_max_trans else {}


def input_drive_cell(lib, pins, name):
    """The driver of every primary input (`name`, from `input_drive_of`): a buffer or inverter of the liberty (one input,
    one output, one arc, function A or !A), or the flop's Q (`FlopDrive`). PpaError otherwise."""
    check_input_drive(name, pins)
    if name == pins.full(pins.flop_cell):
        if pins.flop["q_inverter"]:
            raise PpaError(f"the input drive {name} has no Q output (its Q is formed by an inverter, flop.q_inverter): "
                           "it cannot drive the inputs")
        return FlopDrive(FlopTiming(lib, pins))
    c = lib.cell(name)
    fn = re.sub(r"[\s()]", "", c.function.get(c.outputs[0]) or "") if len(c.outputs) == 1 else ""
    if len(c.inputs) != 1 or len(c.outputs) != 1 or len(c.arcs[c.outputs[0]]) != 1 or \
            fn not in (c.inputs[0], "!" + c.inputs[0]):
        raise PpaError(f"the input drive {name} is not a one-input, one-output, one-arc buffer or inverter in the liberty")
    return c


def cut_flops(nl, flops):
    """The flops of a clocked scored netlist cut out of the timing graph: their Q nets become primary inputs of `nl` (appended,
    in flop order), their D nets endpoints. Returns (Q nets, D nets), resolved."""
    for f in flops:
        if set(f.pins) != {"C", "D", "Q"}:
            raise PpaError(f"flop {f.inst} ($_DFF_P_) has pins {sorted(f.pins)}, expected ['C', 'D', 'Q']")
    q = [nl.resolve(f.pins["Q"]) for f in flops]
    dn = [nl.resolve(f.pins["D"]) for f in flops]
    nl.pi = nl.pi + [x for x in dict.fromkeys(q) if x not in nl.pi]
    return q, dn


def weigh_cells(nl, q, dn, nflops, lib, pins, drive=None, audit=None, ties=None):
    """The STA, area and histogram of a netlist of liberty cells `nl` (a clocked one with its `nflops` flops already cut out
    by `cut_flops`: `q` / `dn` their Q / D nets). `drive`: the Cell driving every primary input (sky130_a0_v3), or None (an
    ideal ramp, flow A1'). `audit`: an Audit, which then also receives the legality checks (every read outside a table, every
    load over max_capacitance, every transition over max_transition, every tie cell output over its max_capacitance); None: a
    read outside a table raises TableRange.

    Constants are the nets "0" and "1" (no arrival, no delay effect). `ties`: the tie cells that drive them, ([the pins' short
    name of each tie cell instance], [(instance, tie cell short name, output pin, constant, load in pF, what it drives)] for
    every output that drives something) as `read_repaired` finds them in a repaired netlist; None: ONE tie cell per module
    if any constant is read (sky130's conb_1: its LO driving every "0" load and its HI every "1" load), one per constant used
    where the library has a cell per constant (asap7: TIELO, TIEHI) (the unrepaired netlist). Each tie output's load is
    audited against its pin's max_capacitance, or the pins' constants.max_capacitance_ff where the cell declares none (it
    has no timing arcs, so nothing else).

    Clocked: each flop is the pins' flop cell (dfxtp_1; its area counts) and cuts the timing graph. Paths start at the inputs
    and at every Q (clock-to-Q at the ideal clock edge, the clock's transition pi_slew, at the Q net's real load) and end at
    the outputs and at every D (arrival + setup): T is the register-to-register period (decided 2026-11-03: the liberty's own
    clock-to-Q and setup)."""
    d = Design(nl, lib, pins)
    s, po = pins.pi_slew_ns, pins.po_load_pf
    starts, ends, sources, sink_trans = {}, [], [], {}
    if nflops:
        ft = FlopTiming(lib, pins)
        for n in dn:
            d.extra_load[n] += ft.d_cap
            for e in "rf":
                d.extra_load_e[e][n] += ft.d_cap_e[e]
            if ft.d_max_trans:
                sink_trans.setdefault(n, []).append(ft.d_max_trans)
        for x in dict.fromkeys(q):
            if d.load_pf(x, po) <= 0.0 and drive is not None:      # a Q nothing reads: no arrival is needed
                continue
            where = ("Q", x, ft.name)
            starts[x] = {e: (_read(ft.cq["cell_" + w], s, d.load_edge_pf(x, po, e), audit, where),
                             _read(ft.cq[w + "_transition"], s, d.load_edge_pf(x, po, e), audit, where))
                         for e, w in (("r", "rise"), ("f", "fall"))}
            sources.append((x, ft.name, "Q", ft.q_max_cap, ft.q_max_trans))

        def setup_at(net):
            return lambda e, slew: _read(ft.setup["rise_constraint" if e == "r" else "fall_constraint"], s, slew, audit,
                                         ("D", net, ft.name))
        ends = [(n, setup_at(n)) for n in dn]
    a = Analysis()
    a.t_ns, a.path = d.sta(s, po, starts, ends, drive, audit)
    if ties is None:
        used = [k for k in "01" if k in d.fanout or k in d.po_count or k in d.extra_load]
        kinds = list(dict.fromkeys(pins.tie_cells[k] for k in used))       # one cell per distinct tie cell used
        ties = (kinds, [(pins.tie_cells[k], pins.tie_cells[k], tie_pins(lib.cell(pins.full(pins.tie_cells[k])), k)[k], k,
                         d.load_max_pf(k, po), d.sinks_text(k, len(sink_trans.get(k, ())))) for k in used])
    a.ties = len(ties[0])
    if isinstance(audit, Audit):
        if drive is not None:
            op = drive.outputs[0]
            qs = set(starts)
            sources += [(n, drive.name, "(input driver)", drive.max_cap.get(op), drive.max_trans.get(op))
                        for n in nl.pi if n not in qs]
        tie_checks = []
        for inst, cname, pin, k, load, what in ties[1]:
            mc = tie_max_cap(lib.cell(pins.full(cname)), pin, pins)
            if mc:
                tie_checks.append((inst, cname, pin, k, load, mc, what))
        d.legality(po, audit, lib.default_max_transition, sources, sink_trans, tie_checks)
        a.audit = audit
    a.unit_depth = d.unit_depth(ends)
    a.area_e4 = sum(c.area_e4 for c in d.cells)
    hist = defaultdict(int)
    for c in d.cells:
        hist[pins.short(c.name)] += 1
    a.cells, a.constants = len(d.cells), d.uses_constant or a.ties > 0
    if nflops:
        a.area_e4 += nflops * ft.area_e4
        hist[pins.flop_cell] += nflops
        a.cells += nflops
        a.flops = nflops
    for k in ties[0]:          # constants policy: the tie cells (no delay effect)
        a.area_e4 += lib.cell(pins.full(k)).area_e4
        a.cells += 1
        hist[k] += 1
    a.hist = dict(sorted(hist.items()))
    if a.path:
        net, a.crit_edge = a.path[-1][0], a.path[-1][1]
        # report the output port bit (the netlist's own name), not the internal net it resolves to
        a.crit_output = next((n for _, _, n in nl.po if nl.resolve(n) == net), ("D:" + net) if nflops else net)
    a.crit_cells = sum(1 for net, _, _ in a.path if net in d.driver)
    a.design = d
    return a


def analyze_cells(nl, lib, pins):
    """Weigh a combinational netlist whose gates are already liberty cells (flow A1''s `abc -liberty` mapping) exactly as
    sky130_a1_v1 always did: ideal 50 ps input ramps, no repair, no legality audit, linear extrapolation outside a table's
    grid (A1_EXTRAPOLATES; the ranked flow never extrapolates)."""
    return weigh_cells(nl, [], [], 0, lib, pins, audit=A1_EXTRAPOLATES)


# ------------------------------------------------------------------------------------------------ the repair (sky130_a0_v2)
class IllegalNetlist(PpaError):
    """The sky130 netlist is electrically illegal (a load over max_capacitance, a transition over max_transition, a timing
    table read outside its characterized range) and the repair cannot make it legal: the design is REJECTED (decided 2026-11-04:
    an illegal netlist is rejected outright). `summary`: the Audit's counts."""

    def __init__(self, msg, summary=None):
        super().__init__(msg)
        self.summary = summary or {}


class RepairDefect(PpaError):
    """The repaired netlist disagrees with the scored one in FUNCTION, cannot be read back, or is not legal although the repair
    found it legal: a defect of the repair or of this reader, not a property of the design (check.py: an infrastructure error
    under `require`, as MappedDefect)."""


def tie_pins(cell, need="01"):
    """{"0": the tie cell's constant-0 output pin, "1": its constant-1 output pin} (conb_1: LO and HI; asap7's TIELOx1 has
    only "0": L, its TIEHIx1 only "1": H), from the liberty; `need`: the constants the cell must have."""
    out = {}
    for p in cell.outputs:
        fn = (cell.function.get(p) or "").replace("(", "").replace(")", "").replace('"', "").strip()
        if fn in ("0", "1"):
            out[fn] = p
    if not set(need) <= set(out) or not out or cell.inputs:
        raise PpaError(f"liberty: the tie cell {cell.name} has no " + " and ".join(f"constant-{k}" for k in need)
                       + (" outputs" if len(need) > 1 else " output"))
    return out


def tie_max_cap(cell, pin, pins):
    """The load the tie cell's output `pin` may carry: its max_capacitance, else the pins' constants.max_capacitance_ff
    (asap7's TIEHI/TIELO declare none), else None (no limit)."""
    return cell.max_cap.get(pin) or pins.tie_max_cap_pf


def _count(k, word):
    return f"{k} {word}" + ("" if k == 1 else "s")


def _nat(s):
    """A natural sort key: `_9_` before `_10_`, `y[2]` before `y[10]`."""
    return tuple((0, int(t), "") if t.isdigit() else (1, 0, t) for t in re.findall(r"\d+|\D+", s))


def load_budget(arcs, s_lo, s_hi, limit, max_cap):
    """The largest load (pF) a driver may carry: within `max_cap` and every table's characterized loads, and such that the
    output transition of every arc in `arcs` (each a {table name: Table}), both edges, stays within `limit` (ns) for every
    input transition in [s_lo, s_hi]. The tables are bilinear, so in the input transition the worst case is at a grid point
    or an end of the range; in the load, the bound is found by bisection (64 halvings: deterministic). 0.0 when even the
    smallest characterized load is over the limit."""
    tables = [t for a in arcs for t in a.values()]
    trans = [a[k] for a in arcs for k in ("rise_transition", "fall_transition")]
    lo = max(t.i2[0] for t in tables)
    hi = min([t.i2[-1] for t in tables] + ([max_cap] if max_cap else []))
    pts = [sorted({s_lo, s_hi} | {x for x in t.i1 if s_lo < x < s_hi}) for t in trans]

    def worst(load):
        return max(t._bilinear(s, load) for t, ps in zip(trans, pts) for s in ps)
    if hi < lo or worst(lo) > limit:
        return 0.0
    if worst(hi) <= limit:
        return hi
    a, b = lo, hi
    for _ in range(64):
        m = (a + b) / 2
        if worst(m) <= limit:
            a = m
        else:
            b = m
    return a


class Budgets:
    """The loads the repair lets each driver carry (`load_budget`), from the liberty alone. The transition limit of a net is
    min(its driver's max_transition, the library's default_max_transition, the most any pin it reaches accepts: 1.5 ns for
    every sky130_fd_sc_hd input); a cell inside the netlist may see any input transition up to that default (the most a legal
    net carries), the primary inputs' input drive (the task's) exactly the pinned input ramp, a flop's Q the ideal clock's
    ramp. A tree built within these budgets is legal whatever the rest of the netlist does, as long as its own input is."""

    def __init__(self, lib, pins, drive, ft):
        self.lib, self.pins, self.drive, self.ft = lib, pins, drive, ft
        self.dmt = lib.default_max_transition or float("inf")
        self._cache = {}
        self.buffers = []          # (area_e4, short name, Cell, budget), by area then name
        for b in pins.repair_buffers:
            c = lib.cell(pins.full(b))
            fn = (c.function.get(c.outputs[0]) or "").replace("(", "").replace(")", "").strip() if c.outputs else ""
            if pins_class(c.name, pins) != "logic" or len(c.inputs) != 1 or len(c.outputs) != 1 or fn != c.inputs[0]:
                raise PpaError(f"pins: repair.buffers names {b}, which is not a one-input, one-output logic buffer")
            self.buffers.append((c.area_e4, b, c, self.cell(c, c.outputs[0])))
        self.buffers.sort(key=lambda x: (x[0], x[1]))

    def _limit(self, mt):
        return min(mt or self.dmt, self.dmt)

    def cell(self, c, pin):
        key = (c.name, pin)
        if key not in self._cache:
            arcs = [a.tbl for a in c.arcs[pin]]
            if not arcs:
                self._cache[key] = c.max_cap.get(pin) or 0.0
            else:
                tabs = [t for a in arcs for t in a.values()]
                s_lo = max(t.i1[0] for t in tabs)
                s_hi = min([self.dmt] + [t.i1[-1] for t in tabs])
                self._cache[key] = load_budget(arcs, s_lo, s_hi, self._limit(c.max_trans.get(pin)), c.max_cap.get(pin))
        return self._cache[key]

    def pi(self):
        d, s = self.drive, self.pins.pi_slew_ns
        op = d.outputs[0]
        return load_budget([a.tbl for a in d.arcs[op]], s, s, self._limit(d.max_trans.get(op)), d.max_cap.get(op))

    def q(self):
        s = self.pins.pi_slew_ns
        return load_budget([self.ft.cq], s, s, self._limit(self.ft.q_max_trans), self.ft.q_max_cap)


def _split(items, k):
    """`items` [(key, cap, ref)], in order, cut into k contiguous non-empty groups balanced by capacitance: the j-th cut at the
    prefix sum nearest to j/k of the total (the earlier one on a tie)."""
    pre = [0.0]
    for _, c, _ in items:
        pre.append(pre[-1] + c)
    n, total, cuts = len(items), pre[-1], [0]
    for j in range(1, k):
        lo, hi, target = cuts[-1] + 1, n - (k - j), total * j / k
        i = min(max(bisect.bisect_left(pre, target, lo, hi + 1), lo), hi)
        if i > lo and abs(pre[i - 1] - target) <= abs(pre[i] - target):
            i -= 1
        cuts.append(i)
    cuts.append(n)
    return [items[cuts[j]:cuts[j + 1]] for j in range(k)]


def _groups(items, cap):
    """The fewest balanced groups (`_split`) of `items` whose loads are all within `cap`, or None if one item is over it."""
    if max(c for _, c, _ in items) > cap:
        return None
    k = max(1, math.ceil(sum(c for _, c, _ in items) / cap))
    while True:
        gs = _split(items, k)
        if all(sum(c for _, c, _ in g) <= cap for g in gs):
            return gs
        k += 1


def _level(items, budgets, scale):
    """One level of a buffer tree over `items`: for each buffer cell the fewest balanced groups within its budget x `scale`;
    the cell and grouping of least total area wins (then fewer groups, then the cell order); each group is then driven by the
    smallest buffer (area, then name) whose budget x `scale` holds its load. [(buffer, group, load)], or None."""
    best = None
    for area, name, cell, bud in budgets.buffers:
        gs = _groups(items, bud * scale)
        if gs is not None and (best is None or (len(gs) * area, len(gs)) < best[0]):
            best = ((len(gs) * area, len(gs)), gs)
    if best is None:
        return None
    out = []
    for g in best[1]:
        load = sum(c for _, c, _ in g)
        out.append((next(b for b in budgets.buffers if b[3] * scale >= load), g, load))
    return out


class _Unfixable(Exception):
    pass


def _tree(items, top, budgets, scale):
    """The levels of the balanced buffer tree that brings the load `items` puts on a driver within its budget `top` (all
    budgets x `scale`), from the loads up: [[(buffer, group, load)], ...]. Raises _Unfixable."""
    levels = []
    while sum(c for _, c, _ in items) > top * scale:
        lv = _level(items, budgets, scale)
        nxt = None if lv is None else [(g[0][0], max(b[2].pin_cap_e[b[2].inputs[0]].values()), ("buf", len(levels), k))
                                       for k, (b, g, _) in enumerate(lv)]
        if lv is None:
            raise _Unfixable("one of its loads alone is more than any buffer of the pins' repair.buffers may drive")
        if sum(c for _, c, _ in nxt) >= sum(c for _, c, _ in items) or len(levels) > 64:
            raise _Unfixable(f"its driver may carry at most {top * scale * 1000:.1f} fF, less than the buffers it would "
                             "need")
        levels.append(lv)
        items = nxt
    return levels


class Repair:
    """The repair of one A0' netlist (sky130_a0_v2, `buffer_trees_v1`; pins: repair, constants). See `repair`."""

    def __init__(self, base, inputs, q, dn, flops, lib, pins, drive):
        self.base, self.q, self.dn, self.flops, self.lib, self.pins, self.drive = base, q, dn, flops, lib, pins, drive
        self.inputs = inputs
        self.ft = FlopTiming(lib, pins) if flops else None
        self.budgets = Budgets(lib, pins, drive, self.ft)
        self.qset = set(q)
        nl = base.nl
        # every load of every net, in the stable order: cell pins (instance, pin), output bits (port, bit), flop D pins; a
        # pin's load is the larger of its rise_capacitance and fall_capacitance, so that a group within a budget is within it
        # on both edges (the timing and the max_capacitance check read each edge: `Design.load_edge_pf`)
        order = {p: k for k, (p, _, _) in enumerate(nl.ports)}
        self.sinks = defaultdict(list)
        for net, lst in base.fanout.items():
            for i, p in lst:
                self.sinks[net].append(((0, _nat(base.names[i]), p), max(base.cells[i].pin_cap_e[p].values()),
                                        ("cell", i, p)))
        for j, (port, k, n) in enumerate(nl.po):
            self.sinks[nl.resolve(n)].append(((1, order[port], k), pins.po_load_pf, ("po", j)))
        for f, n in enumerate(dn):
            self.sinks[n].append(((2, _nat(flops[f].inst), f), max(self.ft.d_cap_e.values()), ("d", f)))
        for lst in self.sinks.values():
            lst.sort(key=lambda s: s[0])
        names = set(base.driver) | set(nl.pi) | set(base.names) | {f.inst for f in flops} | {p for p, _, _ in nl.ports}
        self.prefix = "svgr"
        while any(x.lstrip("\\").startswith(self.prefix) for x in names):
            self.prefix += "_"

    def driver(self, net):
        """(budget, text) of the driver of an original net."""
        base = self.base
        if net in base.driver:
            i, p = base.driver[net]
            return self.budgets.cell(base.cells[i], p), f"{self.pins.short(base.cells[i].name)} {base.names[i]}"
        if net in self.qset:
            f = self.flops[self.q.index(net)]
            return self.budgets.q(), f"the Q of flop {f.inst}"
        return self.budgets.pi(), f"input {net} (driven by {self.pins.short(self.drive.name)})"

    def describe(self, net):
        """An original net in the design's own words, for a message: what drives it and what it drives."""
        _, who = self.driver(net)
        what = self.base.sinks_text(net, sum(1 for n in self.dn if n == net))
        return (f"input {net}" if who.startswith("input") else f"net {net} ({who})") + f", driving {what}"

    def build(self, roots):
        """The A0' netlist with a buffer tree on every net of `roots` {net: budget scale}: (Netlist, D nets, {buffer output net:
        its root}, [(root, [tree level descriptions], buffers, the load its driver may carry)])."""
        base = self.base
        nl = Netlist()
        nl.name, nl.ports, nl.ranges, nl.pi = base.nl.name, base.nl.ports, base.nl.ranges, list(base.nl.pi)
        nl.gates = [Gate(g.kind, g.inst, {**base.ins[i], **base.outs[i]}) for i, g in enumerate(base.nl.gates)]
        nl.po = [(p, k, base.nl.resolve(n)) for p, k, n in base.nl.po]
        dn = list(self.dn)
        owner, trees, k = {}, [], 0
        for r in sorted(roots, key=_nat):
            top, _ = self.driver(r)
            try:
                levels = _tree(self.sinks[r], top, self.budgets, roots[r])
            except _Unfixable as e:
                raise IllegalNetlist(self.reject(f"the {self.describe(r)}: {e}"))
            made, desc = [], []
            for li, lv in enumerate(levels):
                row = []
                for b, g, load in lv:
                    cell = b[2]
                    inst, net = f"{self.prefix}{k}", f"{self.prefix}{k}_x"
                    k += 1
                    nl.gates.append(Gate(cell.name, inst, {cell.inputs[0]: None, cell.outputs[0]: net}))
                    gi = len(nl.gates) - 1
                    owner[net] = r
                    row.append(gi)
                    for _, _, ref in g:
                        if ref[0] == "cell":
                            nl.gates[ref[1]].pins[ref[2]] = net
                        elif ref[0] == "po":
                            p, kk, _ = nl.po[ref[1]]
                            nl.po[ref[1]] = (p, kk, net)
                        elif ref[0] == "d":
                            dn[ref[1]] = net
                        else:                                   # a buffer of the level below
                            bg = nl.gates[made[ref[1]][ref[2]]]
                            bg.pins[next(iter(bg.pins))] = net
                made.append(row)
                hist = defaultdict(int)
                for b, _, _ in lv:
                    hist[b[1]] += 1
                desc.append(" + ".join(f"{n} x {c}" for c, n in sorted(hist.items(), key=lambda x: _nat(x[0]))))
            for gi in made[-1]:
                g = nl.gates[gi]
                g.pins[next(iter(g.pins))] = r
            trees.append((r, desc, [nl.gates[gi] for row in made for gi in row], top * roots[r]))
        return nl, dn, owner, trees

    def reject(self, why, audit=None):
        return (f"the {self.pins.pdk} netlist is electrically illegal and the repair (buffer trees, replicated tie cells) "
                f"cannot make it legal: {why}" + (". " + audit.report() if audit is not None else "")
                + f". The {score_name(self.pins)} ({self.pins.version}) is taken on a legal netlist only (no timing table is "
                "extrapolated), so the design is rejected")

    def run(self):
        """Weigh, buffer every net that is the cause of a violation, weigh again, until legal (at most pins.repair_max_rounds
        rounds). Returns (Netlist, D nets, trees, rounds)."""
        roots = {}
        for rnd in range(1, self.pins.repair_max_rounds + 1):
            nl, dn, owner, trees = self.build(roots)
            audit = new_audit(self.pins)
            a = weigh_cells(nl, self.q, dn, len(self.flops), self.lib, self.pins, self.drive, audit, ties=([], []))
            blame = {n: k for n, k in audit.blame.items() if n not in ("0", "1")}
            if not blame:
                return nl, dn, trees, rnd
            low = [n for n in sorted(blame, key=_nat) if "low" in blame[n]]
            if low:
                raise IllegalNetlist(self.reject(f"a timing table is read BELOW its characterized range at net {low[0]} (a "
                                                 "transition or a load smaller than the library characterizes; no buffer "
                                                 "changes that)", audit), audit.summary())
            d, changed, halved = a.design, False, set()
            for n in sorted(blame, key=_nat):
                kinds = blame[n]
                drv = d.driver.get(n)
                if kinds <= {"trans"} and drv and any(x in blame for x in d.ins[drv[0]].values()):
                    continue                     # slow only because its input is: that input's repair comes first
                root = owner.get(n, n if n in roots else None)
                if root is None:
                    roots[n], changed = 1.0, True
                elif root not in halved:
                    halved.add(root)
                    roots[root] /= 2
                    changed = True
                    if roots[root] < 1 / 64:
                        raise IllegalNetlist(self.reject(f"the {self.describe(root)} stays illegal however its buffer tree "
                                                         "is built", audit), audit.summary())
            if not changed:
                raise IllegalNetlist(self.reject("no net left to buffer", audit), audit.summary())
        raise IllegalNetlist(self.reject(f"still illegal after {self.pins.repair_max_rounds} rounds", audit),
                             audit.summary())

    def ties(self):
        """The tie cells: [(Cell, {constant: (its output pin, group of loads)})], as few as hold every constant load within
        the max_capacitance of the output that drives it (`tie_max_cap`), the loads split as the trees' are (`_groups`). A
        tie cell with both constants (sky130's conb_1) serves the j-th group of each; a library with a cell per constant
        (asap7's TIELOx1, TIEHIx1) has one cell per group."""
        if not (self.sinks.get("0") or self.sinks.get("1")):
            return []
        pins, groups = self.pins, {}
        for k in "01":
            items = self.sinks.get(k, [])
            if items:
                cell = self.lib.cell(pins.full(pins.tie_cells[k]))
                pin = tie_pins(cell, k)[k]
                gs = _groups(items, tie_max_cap(cell, pin, pins) or float("inf"))
                if gs is None:
                    raise IllegalNetlist(self.reject(f"one load of the constant {k} alone is over the max_capacitance of "
                                                     f"{pins.tie_cells[k]} {pin}"))
                groups[k] = (cell, pin, gs)
        if pins.tie_cells["0"] == pins.tie_cells["1"]:
            cell = next(iter(groups.values()))[0]
            n = max(len(g[2]) for g in groups.values())
            return [(cell, {k: (groups[k][1], groups[k][2][j]) for k in groups if j < len(groups[k][2])}) for j in range(n)]
        return [(groups[k][0], {k: (groups[k][1], g)}) for k in "01" if k in groups for g in groups[k][2]]

    def write(self, nl, dn, trees):
        """The repaired netlist as structural Verilog: the ports as declared, every A0' cell, the buffer trees (a comment each
        naming the net, its driver and its loads), the tie cells, the flops (dfxtp_1), an `assign` per output bit. Nets keep
        their names (a net named as the output bit it drives is that port bit; a name that is not a plain identifier is
        escaped; one that would clash with a port, e.g. an output bit's name when the bit now hangs off a buffer, gets a `$`)."""
        pins = self.pins
        ties = self.ties()
        inputs = set(self.inputs)
        port_names = {p for p, _, _ in nl.ports}
        # a net named as the output bit it drives (Yosys's own naming) IS that port bit, as in the scored netlist
        own = {n for p, k, n in nl.po if n == nl.port_bit(p, k)}
        used, wname = set(), {}

        def w(n):
            if n not in wname:
                if n in inputs or n in own:
                    x = n
                elif n.startswith("\\"):
                    x = n + " "
                elif re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", n):
                    x = n
                    while x in port_names or x in used:
                        x += "$"
                else:
                    x = "\\" + n + " "
                while x in used:
                    x = x.rstrip() + "$ " if x.endswith(" ") else x + "$"
                used.add(x)
                wname[n] = x
            return wname[n]
        for n in sorted(inputs | own, key=_nat):
            w(n)
        # the tie cells' nets, and where each constant load goes
        tie_net = {}
        tie_gates = []
        for j, (tie, grp) in enumerate(ties):
            inst = f"{self.prefix}t{j}"
            pn = {p: f"{self.prefix}t{j}_{p.lower()}" for p in tie.outputs}
            tie_gates.append(Gate(tie.name, inst, pn))
            for k, (pin, items) in grp.items():
                for _, _, ref in items:
                    tie_net[ref] = pn[pin]

        def inp(i, p, n):              # a cell input: a constant becomes its tie cell's output
            return tie_net[("cell", i, p)] if n in ("0", "1") else n
        nb = sum(len(t[2]) for t in trees)
        lines = [f"/* {pins.version}: the A0' netlist of module {nl.name} after the repair (score/ppa.py, {pins.repair_method}): "
                 f"{_count(nb, 'buffer')} on {_count(len(trees), 'net')}, {_count(len(ties), 'tie cell')}. */",
                 f"module {nl.name}(" + ", ".join(p for p, _, _ in nl.ports) + ");"]
        for p, direction, width in nl.ports:
            r = nl.ranges.get(p)
            lines.append(f"  {direction} " + (f"[{r[0]}:{r[1]}] " if r else "") + f"{p};")
        body, wires = [], []

        def inst_line(g, conns):
            inst = g.inst + " " if g.inst.startswith("\\") else g.inst
            return f"  {g.kind} {inst} (" + ", ".join(f".{p}({c})" for p, c in conns) + ");"
        nbase = len(self.base.nl.gates)
        for i, g in enumerate(nl.gates[:nbase]):
            c = self.base.cells[i]
            conns = []
            for p, n in g.pins.items():
                if p in c.inputs:
                    conns.append((p, w(inp(i, p, n)) if n in ("0", "1") else w(n)))
                else:
                    conns.append((p, w(n)))
                    wires.append(n)
            body.append(inst_line(g, conns))
        for r, desc, bufs, budget in trees:
            load = sum(c for _, c, _ in self.sinks[r])
            note = (f"repair: the {self.describe(r)}: {load * 1000:.1f} fF, over the {budget * 1000:.1f} fF its driver may "
                    "carry; a balanced tree of " + ", then ".join(reversed(desc)) + " (from the driver down)")
            body.append("  /* " + note.replace("*/", "* /") + " */")
            for g in bufs:
                (pa, a), (px, x) = list(g.pins.items())
                wires.append(x)
                body.append(inst_line(g, [(pa, w(a)), (px, w(x))]))
        if tie_gates and pins.tie_cell is not None:
            body.append(f"  /* constants: {len(tie_gates)} {pins.tie_cell} tie cell{'s' if len(tie_gates) > 1 else ''} */")
        elif tie_gates:
            kinds = defaultdict(int)
            for g in tie_gates:
                kinds[pins.short(g.kind)] += 1
            body.append("  /* constants: " + " + ".join(f"{n} {c}" for c, n in sorted(kinds.items()))
                        + f" tie cell{'s' if len(tie_gates) > 1 else ''} */")
        for g in tie_gates:
            for n in g.pins.values():
                wires.append(n)
            body.append(inst_line(g, [(p, w(n)) for p, n in g.pins.items()]))
        for f, g in enumerate(self.flops):
            d = dn[f]
            d = tie_net[("d", f)] if d in ("0", "1") else d
            q = self.q[f]
            wires.append(q)
            fp = pins.flop
            body.append(inst_line(Gate(pins.full(pins.flop_cell), g.inst, {}),
                                  [(fp["clock"], w(self.base.nl.resolve(g.pins["C"]))), (fp["d"], w(d)), (fp["q"], w(q))]))
        assigns = []
        for j, (p, k, n) in enumerate(nl.po):
            n = tie_net[("po", j)] if n in ("0", "1") else n
            if n != nl.port_bit(p, k):
                assigns.append(f"  assign {nl.port_bit(p, k)} = {w(n)};")
        decl = [f"  wire {w(n)};" for n in dict.fromkeys(wires) if n not in inputs and n not in own]
        return "\n".join(lines + decl + body + assigns + ["endmodule", ""])


def repair(base, inputs, q, dn, flops, lib, pins, drive):
    """The A0' cell netlist `base` (a Design; flops cut out: `q` / `dn` their Q / D nets, `flops` the $_DFF_P_ gates) REPAIRED
    (sky130_a0_v2, decided 2026-11-04: every netlist is repaired, by buffering; pins: repair, constants), by buffering only:

      * weigh it (inputs driven by `drive`, the task's input drive; every output bit a separate po_load; every flop D pin a
        load) and audit it; every net that is the CAUSE of a violation (its load over its driver's max_capacitance or past
        its tables, or its transition over a limit while its driver's inputs are legal) gets a balanced buffer tree
        (`_tree`: the loads in a stable order, split into contiguous groups balanced by capacitance, level by level, each
        level the buffer cell and group count of least area within the cells' budgets, `Budgets`); primary-input nets, flop
        Q nets and nets that drive output bits are buffered like any other;
      * weigh again and repeat until no violation is left (a tree still illegal is rebuilt at half its budgets); a netlist
        that cannot be made legal raises IllegalNetlist, naming the net in the design's words;
      * the constants: as few tie cells as hold every constant load within its output's max_capacitance (`Repair.ties`).

    No cell is resized, no logic is restructured. Returns (the repaired netlist as structural Verilog text, its record:
    buffers, nets buffered, tie cells, rounds)."""
    rp = Repair(base, inputs, q, dn, flops, lib, pins, drive)
    nl, rdn, trees, rounds = rp.run()
    text = rp.write(nl, rdn, trees)
    return text, {"buffers": sum(len(t[2]) for t in trees), "nets": len(trees), "rounds": rounds}


def read_repaired(text, lib, pins):
    """A repaired netlist (`Repair.write`) as the weighing reads it: its tie cells become the constants they drive (each
    output's load recorded for the audit), its flops (the pins' flop cell: dfxtp_1) $_DFF_P_ gates (pins C, D, Q; asap7:
    Q is the cell's QN, which the Q inverter reads) to be cut out as in the scored netlist. Returns (Netlist, flops, ties
    as weigh_cells takes them, the input bits)."""
    try:
        nl = parse_netlist(text)
    except PpaError as e:
        raise RepairDefect(f"the repaired netlist cannot be read back: {e}")
    fp = pins.flop
    flop_kind = pins.full(pins.flop_cell)
    tie_kinds = {pins.full(c) for c in pins.tie_cells.values()}
    val = {k: {p: c for c, p in tie_pins(lib.cell(k), "").items()} for k in tie_kinds
           if any(g.kind == k for g in nl.gates)}        # tie cell -> {output pin: its constant}
    ties, flops, gates = [], [], []
    for g in nl.gates:
        if g.kind in tie_kinds:
            ties.append(g)
        elif g.kind == flop_kind:
            if set(g.pins) != {fp["clock"], fp["d"], fp["q"]}:
                raise RepairDefect(f"the repaired netlist's flop {g.inst} has pins {sorted(g.pins)}")
            flops.append(Gate(FLOP_KIND, g.inst, {"C": g.pins[fp["clock"]], "D": g.pins[fp["d"]], "Q": g.pins[fp["q"]]}))
        else:
            gates.append(g)
    nl.gates = gates
    tnet = {}
    for g in ties:
        for p, n in g.pins.items():
            if p not in val[g.kind] or n in tnet:
                raise RepairDefect(f"the repaired netlist's tie cell {g.inst} is not connected as written")
            tnet[n] = (g.inst, pins.short(g.kind), p, val[g.kind][p])
    load_e, bits, cells, dpins = {"r": defaultdict(float), "f": defaultdict(float)}, defaultdict(list), defaultdict(int), \
        defaultdict(int)
    for g in gates:
        c = lib.cell(g.kind) if lib.has(g.kind) else None
        for p, n in g.pins.items():
            r = nl.resolve(n)
            if c is not None and p in c.inputs and r in tnet:
                for e in "rf":
                    load_e[e][r] += c.pin_cap_e[p][e]
                cells[r] += 1
    for port, k, n in nl.po:
        r = nl.resolve(n)
        if r in tnet:
            for e in "rf":
                load_e[e][r] += pins.po_load_pf
            bits[r].append(nl.port_bit(port, k))
    if flops:
        d_cap_e = FlopTiming(lib, pins).d_cap_e
        for f in flops:
            r = nl.resolve(f.pins["D"])
            if r in tnet:
                for e in "rf":
                    load_e[e][r] += d_cap_e[e]
                dpins[r] += 1
    load = {n: max(load_e["r"][n], load_e["f"][n]) for n in tnet}     # the larger edge's, as the audit checks
    checks = []
    for n, (inst, cname, p, k) in tnet.items():
        nl.alias[n] = k
        if load[n] > 0:
            what = [f"{len(bits[n])} output bit{'s' if len(bits[n]) > 1 else ''} ({bits[n][0]}"
                    + (f" .. {bits[n][-1]})" if len(bits[n]) > 1 else ")")] if bits[n] else []
            what += [f"{cells[n]} cell pin{'s' if cells[n] > 1 else ''}"] if cells[n] else []
            what += [f"{dpins[n]} flop D pin{'s' if dpins[n] > 1 else ''}"] if dpins[n] else []
            checks.append((inst, cname, p, k, load[n], ", ".join(what)))
    return nl, flops, ([pins.short(g.kind) for g in ties], checks), list(nl.pi)


def check_repair(base, dn, rd, rdn, pins):
    """The repaired netlist (Design `rd`, flops cut out, `rdn` its D nets) computes what the A0' netlist `base` (`dn`) does on
    the pins' sample (repair.equivalence: every output bit and every flop D net, the flop Q nets driven as inputs, matched by
    position). Raises RepairDefect at the first difference."""
    if len(base.nl.pi) != len(rd.nl.pi) or len(base.po_nets) != len(rd.po_nets) or len(dn) != len(rdn):
        raise RepairDefect("the repaired netlist has other inputs, outputs or flops than the A0' netlist")
    mask = (1 << pins.repair_vectors) - 1
    stim = stimulus(base.nl.pi, pins.repair_vectors, pins.repair_seed)
    va = simulate(base, stim, mask)
    vb = simulate(rd, {b: stim[a] for a, b in zip(base.nl.pi, rd.nl.pi)}, mask)

    def value(v, n):
        return 0 if n == "0" else mask if n == "1" else v[n]
    for k, (x, y) in enumerate(zip(base.po_nets + list(dn), rd.po_nets + list(rdn))):
        a, b = value(va, x), value(vb, y)
        if a != b:
            bit = ((a ^ b) & -(a ^ b)).bit_length() - 1
            where = (f"output {base.nl.port_bit(*base.nl.po[k][:2])}" if k < len(base.po_nets)
                     else f"the D of flop {k - len(base.po_nets)}")
            raise RepairDefect(f"the repaired netlist differs from the A0' netlist at {where} on vector {bit} of "
                               f"{pins.repair_vectors}")


# ------------------------------------------------------------------------------------------------ the ranked weighing
def analyze(netlist_text, lib, pins, repair_netlist=True, input_drive=None):
    """Weigh a scored (`abc -g`) netlist, the ranked flow (sky130_a0_v3): parse, expand each gate to one _1 cell (A0'), cut
    the flops out, REPAIR (`repair`: buffer trees and replicated tie cells, decided 2026-11-04: every netlist
    is repaired, by buffering), write the repaired netlist, read it back, check its function against the A0' netlist, then the STA with
    every primary input driven by `input_drive` (the task's, `input_drive_of`; None: the pins' default), and the legality
    audit (an `input_drive` outside the pins' allowlist raises TaskConfigError). A netlist the repair cannot make legal
    raises IllegalNetlist with the nets named; nothing is extrapolated. The unit depth (`ltp -noff`) and the gate count are
    those of the scored netlist itself (the A0' expansion, unrepaired), the columns score.py's own reading is checked against.
    `repair_netlist=False` (tests and research only: the CLI and check.py always repair) weighs the expansion as it is, with
    the same driving cell and audit (one tie cell)."""
    raw = parse_netlist(netlist_text)
    flops = [g for g in raw.gates if g.kind == FLOP_KIND]
    raw.gates = [g for g in raw.gates if g.kind != FLOP_KIND]
    nl = expand_a0(raw, pins)          # raises on a gate outside the table, so the kinds below are all known
    for gate in sorted({re.fullmatch(r"\$_(\w+?)_", g.kind).group(1) for g in raw.gates}):
        check_gate_cell(lib, pins, gate)
    inputs = list(raw.pi)
    scored_gates = len(raw.gates) + len(flops)     # the scored netlist's gates and flops (score.py's count), not its cells
    if flops:
        FlopTiming(lib, pins)          # the flop cell checked (a positive-edge flop of D; Q formed as the pins say)
    flops = invert_flop_q(nl, flops, pins)
    q, dn = cut_flops(nl, flops)
    base = Design(nl, lib, pins)
    unit_depth = base.unit_depth([(n, None) for n in dn])
    a_drive = input_drive_of(None, pins) if input_drive is None else input_drive
    drive = input_drive_cell(lib, pins, a_drive)
    info, ties = None, None
    if repair_netlist:
        text, info = repair(base, inputs, q, dn, flops, lib, pins, drive)
        info.update(text=text, netlist_sha256=sha256_bytes(text.encode()))
        nl, flops, ties, inputs = read_repaired(text, lib, pins)
        q, rdn = cut_flops(nl, flops)
        try:
            a = weigh_cells(nl, q, rdn, len(flops), lib, pins, drive, new_audit(pins), ties=ties)
        except PpaError as e:
            raise RepairDefect(f"the repaired netlist cannot be weighed: {e}")
        check_repair(base, dn, a.design, rdn, pins)
        dn = rdn
        if a.audit.violations():
            raise RepairDefect("the repaired netlist read back is not legal although the repair found it so: "
                               + a.audit.report())
    else:
        a = weigh_cells(nl, q, dn, len(flops), lib, pins, drive, new_audit(pins))
    a.unit_depth = unit_depth
    a.input_drive = a_drive
    a.scored_gates = scored_gates
    a.repair = info
    a.flop_gates, a.q, a.dn, a.inputs = flops, q, dn, inputs      # for the energy model (score/energy.py)
    if a.audit.violations():
        raise IllegalNetlist(
            f"the {pins.pdk} netlist is electrically illegal (unrepaired). " + a.audit.report()
            + f". The {score_name(pins)} ({pins.version}) is taken on a legal netlist only (no timing table is "
            f"extrapolated), so the design is rejected", a.audit.summary())
    return a


def score_name(pins):
    """How a rejection names the score it withholds: `ranked sky130 score`, `asap7 score`."""
    return f"ranked {pins.pdk} score" if pins.pdk == "sky130" else f"{pins.pdk} score"


def columns(a, pins, lib, netlist_sha256, script_sha256=None, with_path=False):
    """The result block for one weighed netlist: integers where the quantity is exact, versions and pins beside. The
    column names carry the library (`area_um2_sky130`, `area_um2_asap7`, ...; the integer area `area_e4um2_sky130` in
    1e-4 um^2, `area_e5um2_asap7` in 1e-5 um^2), so that the two are never swapped silently."""
    c, d = pins.col, pins.area_decimals
    out = {
        "ppa_version": pins.version,
        f"area_um2_{c}": a.area_e4 / 10 ** d,
        f"area_e{d}um2_{c}": a.area_e4,
        f"delay_ps_{c}": round(a.t_ns * 1000),
        "unit_depth": a.unit_depth,
        f"cells_{c}": a.cells,
        f"cell_hist_{c}": dict(a.hist),
        "constants": a.constants,
        "critical": {"output": a.crit_output, "edge": a.crit_edge, "cells": a.crit_cells},
        "setup": {"pi_slew_ps": pins.pi_slew_ps, "input_drive": a.input_drive,
                  "po_load_ff": pins.po_load_ff, "wires": "none",
                  "tables": "no extrapolation" if pins.below_grid == "reject" else
                  "no extrapolation; a read below a grid at the grid's floor"},
        "liberty_file": pins.lib_file(),
        "liberty_sha256": lib.sha256,
        "ppa_pins_sha256": pins.sha256,
        "ppa_script_sha256": script_sha256 if script_sha256 else sha256_file(os.path.abspath(__file__)),
        "netlist_sha256": netlist_sha256,
    }
    if pins.pdk != "sky130":
        out["pdk"] = pins.pdk
    if pins.multi:             # several files: the set's identity above, each file's here
        out["liberty_files"] = dict(lib.file_sha256)
    if a.audit is not None:
        out["legality"] = a.audit.summary()
    if a.repair is not None:
        out["repair"] = {"method": pins.repair_method,
                         "cells_before": a.scored_gates,       # the scored netlist's gates and flops (score.py's count)
                         "buffers": a.repair["buffers"], "nets_buffered": a.repair["nets"], "tie_cells": a.ties,
                         "rounds": a.repair["rounds"], "netlist_sha256": a.repair["netlist_sha256"]}
    if a.flops is not None:
        out.update({"sequential": True, "flops": a.flops})      # delay_ps_sky130 is then the register-to-register period
    if with_path:
        out["critical_path"] = [[net, edge] for net, edge, _ in a.path]
        out["critical_path_timing"] = path_timing(a, pins)
    return out


def path_timing(a, pins):
    """The critical path of `--path` node by node, as the STA computed it (display only, never ranked): the net, its
    edge, the instance driving it and its cell (None for a primary input or a flop's Q, where the path starts), the
    arrival and the transition at the net in ps (rounded to 0.1 ps). The last node's arrival is the delay (a clocked
    netlist's period adds the capturing flop's setup to it)."""
    d = a.design
    out = []
    for net, edge, t in a.path:
        drv = d.driver.get(net)
        cell = d.cells[drv[0]].name if drv else None
        out.append({"net": net, "edge": edge, "inst": d.names[drv[0]] if drv else None,
                    "cell": pins.short(cell) if cell else cell,
                    "arrival_ps": round(t * 1000, 1), "slew_ps": round(d.arr[(net, edge)][1] * 1000, 1)})
    return out


# ------------------------------------------------------------------------------------------------ flow A1'
MAPPED_PINS_PATH = os.path.join(HERE, "ppa_mapped_pins.json")
MAPPED_SCRIPT_PATH = os.path.join(HERE, "ppa_mapped.ys")


class MappedPins:
    """score/ppa_mapped_pins.json (flow A1') and the script score/ppa_mapped.ys, validated and bound to the A0' pins: the
    liberty must be the same file, so one fetched copy and one hash serve both flows."""

    def __init__(self, pins, path=None, script=None):
        _, dpath, dscript = pdk_paths(pins.pdk)       # the library's own A1' pins and script by default
        path, script = path or dpath, script or dscript
        self.path, self.script = path, script
        try:
            with open(path) as fh:
                raw = json.load(fh)
        except (OSError, ValueError) as e:
            raise PpaError(f"cannot read the mapped-flow pins file {path}: {e}")
        try:
            self.sha256 = sha256_file(path)
            self.script_sha256 = sha256_file(script)
        except OSError as e:
            raise PpaError(f"cannot read the mapped-flow files: {e}")
        try:
            self.version = raw["ppa_mapped_version"]
            self.lib_sha256 = raw["liberty_sha256"]
            self.yosys_version = raw["tools"]["yosys_version"]
            self.abc_version = raw["tools"]["abc_version"]
            self.abc_script = raw["script"]["abc_script"]
            self.equiv_vectors = int(raw["equivalence"]["vectors"])
            self.equiv_seed = raw["equivalence"]["seed"]
            self.timeout_s = int(raw["yosys_timeout_s"])
            # the liberty files ABC maps onto (a library of several files: the combinational ones; default all of them)
            self.abc_files = list(raw.get("abc_liberty_files", [f["file"] for f in pins.lib_files]))
            # the cells counted as buffers and inverters in the record (short-name prefixes)
            cp = raw.get("count_prefixes", {"buffers": ["buf_", "bufbuf_", "bufinv_"], "inverters": ["inv_"]})
            self.buffer_prefixes, self.inverter_prefixes = tuple(cp["buffers"]), tuple(cp["inverters"])
        except (KeyError, TypeError, ValueError) as e:
            raise PpaError(f"mapped-flow pins file {path}: missing or malformed key {e}")
        want = pins.lib["sha256"] if not pins.multi else set_sha256(pins.lib_files)
        if self.lib_sha256 != want:
            raise PpaError(f"the mapped-flow pins name the liberty {self.lib_sha256}, the A0' pins {want}: "
                           "both flows weigh with one liberty")
        if not self.abc_files or not set(self.abc_files) <= {f["file"] for f in pins.lib_files}:
            raise PpaError("mapped-flow pins: abc_liberty_files must name files of the A0' pins' liberty")
        if self.equiv_vectors < 256 or self.equiv_vectors % 256:
            raise PpaError("mapped-flow pins: equivalence.vectors must be a multiple of 256, at least 256")
        if self.timeout_s < 1:
            raise PpaError("mapped-flow pins: yosys_timeout_s must be a positive number of seconds")


def _score_module():
    """score.py, imported on first use (it is not needed to weigh a netlist, only to run Yosys)."""
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    import score
    return score


_ABC_VERSIONS = {}


def abc_version(yosys):
    """The banner of the ABC built into this Yosys (`UC Berkeley, ABC 1.01 (compiled ...)`), read from the `yosys-abc` that
    sits beside the Yosys executable (where Yosys looks for it); None when it cannot be run. Cached per executable."""
    score = _score_module()
    if yosys not in _ABC_VERSIONS:
        exe = os.path.realpath(shutil.which(yosys) or yosys)
        abc = os.path.join(os.path.dirname(exe), "yosys-abc")
        try:
            out = subprocess.run([abc, "-c", "version"], capture_output=True, text=True, timeout=60,
                                 env=score.sandbox.scrubbed_env()).stdout
        except (OSError, subprocess.SubprocessError):
            out = ""
        m = re.search(r"^(UC Berkeley, ABC .*)$", out, re.M)
        _ABC_VERSIONS[yosys] = m.group(1).strip() if m else None
    return _ABC_VERSIONS[yosys]


def map_rtlil(rtlil_path, top, lib, mpins, yosys=None):
    """Flow A1', stage 1: the canonical RTLIL at `rtlil_path` through score/ppa_mapped.ys in a fresh Yosys process (the
    sandbox of score.yosys_run applies where it is active; the liberty and the RTLIL are the only extra reads; at most
    `yosys_timeout_s` of the pins file). Returns the
    mapped netlist text. The liberty's hash was verified when `lib` was opened, and the file Yosys reads is `lib.path`: the
    bytes ABC maps onto are the bytes that were hashed. Raises PpaError (a Yosys failure or timeout is the design's mapping
    failure, not a result)."""
    score = _score_module()
    yosys = score.yosys_bin(yosys)
    # the files ABC reads: the one liberty (sky130), or the pinned subset of a library of several (`-liberty` once each)
    by_name = dict(zip((f["file"] for f in lib.pins.lib_files), lib.paths))
    abc_paths = [os.path.abspath(by_name[f]) for f in mpins.abc_files]
    work = tempfile.mkdtemp(prefix="svgolf-ppa-map-")
    try:
        net = os.path.join(work, "mapped.v")
        text = score.fill_template(mpins.script, {
            "@RTLIL@": f'"{os.path.abspath(rtlil_path)}"', "@TOP@": top,
            "@LIBERTY@": " -liberty ".join(f'"{p}"' for p in abc_paths), "@NETLIST@": f'"{net}"'})
        path, log = os.path.join(work, "map.ys"), os.path.join(work, "map.log")
        with open(path, "w") as fh:
            fh.write(text)
        try:
            proc = score.yosys_run([yosys, "-q", "-l", log, "-s", path], yosys, work,
                                   (os.path.abspath(rtlil_path), *abc_paths), mpins.timeout_s,
                                   "yosys (flow A1' mapping)")
        except subprocess.TimeoutExpired:
            raise PpaError(f"the mapping run timed out after {mpins.timeout_s} s")
        except OSError as e:
            raise PpaError(f"the mapping run could not start: {e}")
        if proc.returncode != 0:
            tail = " ".join((proc.stderr or proc.stdout or "")[-600:].split())
            raise PpaError(f"the mapping run failed (exit {proc.returncode}): {tail}")
        try:
            with open(net, "rb") as fh:
                return fh.read().decode()
        except (OSError, UnicodeDecodeError) as e:
            raise PpaError(f"the mapping run wrote no readable netlist: {e}")
    finally:
        shutil.rmtree(work, ignore_errors=True)


def analyze_mapped(netlist_text, lib, pins):
    """Flow A1', stage 2: weigh a mapped netlist exactly as A0' weighs its expansion (`analyze_cells`: the same checks, the same
    STA, area, histogram and constants policy). Every instance must be a cell of the pinned liberty (the plan's unmapped
    count is zero or the weighing refuses). Returns (the parsed netlist, the Analysis)."""
    nl = parse_netlist(netlist_text)
    bad = defaultdict(int)
    for g in nl.gates:
        if not (g.kind.startswith(pins.prefix) and g.kind.endswith(pins.suffix) and lib.has(g.kind)):
            bad[g.kind] += 1
    if bad:
        raise PpaError(f"the mapped netlist has instances that are not cells of the pinned liberty: {dict(sorted(bad.items()))}")
    return nl, analyze_cells(nl, lib, pins)


# -- the equivalence sample: the mapped netlist against the scored one, bit-parallel through the liberty's own functions
_FN_CODE = {}


def _cell_fn(cell, pin):
    key = (cell.name, pin)
    if key not in _FN_CODE:
        fn = cell.function.get(pin)
        if fn is None:
            raise PpaError(f"liberty cell {cell.name} has no function on output {pin}")
        _FN_CODE[key] = compile(_compile_function(fn), f"<{cell.name}.{pin}>", "eval")
    return _FN_CODE[key]


def stimulus(pi_bits, vectors, seed):
    """The input vectors of the equivalence sample, bit-parallel: one `vectors`-bit integer per primary-input bit, in the order
    of `pi_bits`. Vector 0 is all zeros, vector 1 all ones, the rest are SHA-256(`seed`/`bit index`/`block`) bits."""
    out = {}
    for j, n in enumerate(pi_bits):
        raw = b"".join(hashlib.sha256(f"{seed}/{j}/{c}".encode()).digest() for c in range(vectors // 256))
        out[n] = (int.from_bytes(raw, "little") & ~3) | 2
    return out


def simulate(design, pi_values, mask):
    """Net -> bit-parallel value over `design` (a Design of liberty cells): primary inputs from `pi_values`, constants 0 and
    all-ones."""
    val = dict(pi_values)
    val["0"], val["1"] = 0, mask
    for i in design.order:
        c = design.cells[i]
        env = {p: val[n] for p, n in design.ins[i].items()}
        for op, onet in design.outs[i].items():
            val[onet] = eval(_cell_fn(c, op), {"__builtins__": {}}, {"v": env, "M": mask})
    return val


def check_equivalent(scored_text, mapped_nl, lib, pins, mpins):
    """The mapped netlist `mapped_nl` (parsed) computes the same function as the scored netlist `scored_text` on the sample of
    `mpins.equiv_vectors` vectors: every output bit equal on every vector. Raises PpaError at the first differing bit.
    Returns the number of vectors compared. Both are simulated through the liberty's cell functions (the A0' expansion of the
    scored gates is checked against the Yosys gate semantics by `analyze`)."""
    a = Design(expand_a0(parse_netlist(scored_text), pins), lib, pins)
    b = Design(mapped_nl, lib, pins)
    if a.nl.ports != b.nl.ports or a.nl.pi != b.nl.pi:
        raise MappedDefect("the mapped netlist has other ports than the scored one")
    v = mpins.equiv_vectors
    mask = (1 << v) - 1
    stim = stimulus(a.nl.pi, v, mpins.equiv_seed)
    va, vb = simulate(a, stim, mask), simulate(b, stim, mask)
    for (port, bit, net_a), (_, _, net_b) in zip(a.nl.po, b.nl.po):
        x, y = va[a.nl.resolve(net_a)], vb[b.nl.resolve(net_b)]
        if x != y:
            k = ((x ^ y) & -(x ^ y)).bit_length() - 1
            raise MappedDefect(f"the mapped netlist differs from the scored netlist at output {port}[{bit}] on vector {k} of "
                           f"{v} (scored {(x >> k) & 1}, mapped {(y >> k) & 1})")
    return v


def mapped_columns(a, pins, mpins, lib, mapped_sha256, rtlil_sha256, yosys, abc, equiv_vectors, script_sha256=None,
                   with_path=False):
    """The `mapped` block for one weighed mapped netlist: the A1' fields (their own names and version, never A0''s), the
    hashes of every input and the tool builds."""
    hist = dict(a.hist)
    c, d = pins.col, pins.area_decimals
    out = {
        "ppa_mapped_version": mpins.version,
        f"area_um2_{c}_mapped_v1": a.area_e4 / 10 ** d,
        f"area_e{d}um2_{c}_mapped_v1": a.area_e4,
        f"mapped_delay_{c}_v1": round(a.t_ns * 1000),
        f"mapped_cells_{c}_v1": a.cells,
        f"mapped_cell_hist_{c}_v1": hist,
        f"mapped_levels_{c}_v1": a.unit_depth,
        f"mapped_buffers_{c}_v1": sum(n for x, n in hist.items() if x.startswith(mpins.buffer_prefixes)),
        f"mapped_inverters_{c}_v1": sum(n for x, n in hist.items() if x.startswith(mpins.inverter_prefixes)),
        "constants": a.constants,
        "critical": {"output": a.crit_output, "edge": a.crit_edge, "cells": a.crit_cells},
        "setup": {"pi_slew_ps": pins.pi_slew_ps, "po_load_ff": pins.po_load_ff, "wires": "none"},
        "equivalence": {"vectors": equiv_vectors, "seed": mpins.equiv_seed},
        "liberty_file": pins.lib_file(),
        "liberty_sha256": lib.sha256,
        "ppa_pins_sha256": pins.sha256,
        "ppa_mapped_pins_sha256": mpins.sha256,
        "ppa_mapped_script_sha256": mpins.script_sha256,
        "ppa_script_sha256": script_sha256 if script_sha256 else sha256_file(os.path.abspath(__file__)),
        "yosys_version": yosys,
        "abc_version": abc,
        "rtlil_sha256": rtlil_sha256,
        "netlist_sha256": mapped_sha256,
    }
    if pins.pdk != "sky130":
        out["pdk"] = pins.pdk
    if pins.multi:
        out["liberty_files"] = dict(lib.file_sha256)
        out["abc_liberty_files"] = list(mpins.abc_files)
    if with_path:
        out["critical_path"] = [[net, edge] for net, edge, _ in a.path]
    return out


def weigh_mapped(rtlil_path, top, scored_text, lib, pins, mpins=None, yosys=None, with_path=False, netlist_out=None):
    """Flow A1' on one design: map the canonical RTLIL, check the mapped netlist against the scored one (`scored_text`, the
    netlist the pinned flow wrote and postsynth verified), weigh it. Returns the `mapped` block with `available: true`.
    Raises PpaError: the mapping failed, a cell outside the liberty or its policy, a netlist the reader or the STA cannot
    handle, or a mapped function that differs from the scored one."""
    score = _score_module()
    mpins = mpins or MappedPins(pins)
    try:
        with open(rtlil_path, "rb") as fh:
            rtlil_sha = sha256_bytes(fh.read())
    except OSError as e:
        raise PpaError(f"cannot read the canonical RTLIL {rtlil_path}: {e}")
    text = map_rtlil(rtlil_path, top, lib, mpins, yosys)
    if netlist_out:
        with open(netlist_out, "w") as fh:
            fh.write(text)
    nl, a = analyze_mapped(text, lib, pins)
    vectors = check_equivalent(scored_text, nl, lib, pins, mpins)
    yosys = score.yosys_bin(yosys)
    return dict(mapped_columns(a, pins, mpins, lib, sha256_bytes(text.encode()), rtlil_sha, score.yosys_version(yosys),
                               abc_version(yosys), vectors, with_path=with_path), available=True)


def mapped_block(rtlil_path, top, scored_text, lib, pins, mpins=None, yosys=None, with_path=False, netlist_out=None):
    """`weigh_mapped`, with the loud-reason convention of the `ppa` block: a design the flow cannot map or weigh gives
    `{"available": false, "reason": one line}`, never a number and never a failure of the check. A `MappedDefect` (the mapped
    function differs from the scored one: a defect of the flow, not of the design) propagates."""
    try:
        return weigh_mapped(rtlil_path, top, scored_text, lib, pins, mpins, yosys, with_path, netlist_out)
    except MappedDefect:
        raise
    except PpaError as e:
        return {"available": False, "reason": " ".join(str(e).split())}


# ------------------------------------------------------------------------------------------------ drivers
def open_library(liberty=None, pins=None):
    pins = pins or Pins()
    return Liberty(find_liberty(liberty, pins), pins), pins


def weigh_netlist_text(text, lib, pins, with_path=False, input_drive=None):
    a = analyze(text, lib, pins, input_drive=input_drive)
    return columns(a, pins, lib, sha256_bytes(text.encode()), with_path=with_path)


def weigh_netlist_file(path, liberty=None, pins=None, with_path=False, repaired_out=None, input_drive=None):
    """The PPA columns of an existing scored netlist file (the one postsynth simulates), its inputs driven by
    `input_drive` (`input_drive_of`; None: the pins' default). Raises PpaError."""
    lib, pins = open_library(liberty, pins)
    try:
        with open(path, "rb") as fh:
            data = fh.read()
    except OSError as e:
        raise PpaError(f"cannot read the netlist {path}: {e}")
    try:
        text = data.decode()
    except UnicodeDecodeError as e:
        raise PpaError(f"netlist {path} is not text: {e}")
    a = analyze(text, lib, pins, input_drive=input_drive)
    if repaired_out:
        with open(repaired_out, "w") as fh:
            fh.write(a.repair["text"])
    return columns(a, pins, lib, sha256_bytes(data), with_path=with_path)


def score_and_weigh(sources, top, params, liberty=None, pins=None, yosys=None, repeat=1, gate=True,
                    netlist_out=None, with_path=False, mapped=True, mapped_netlist_out=None, flow="comb", repaired_out=None,
                    input_drive=None):
    """The pinned flow of score.py on `sources` at the scoring point (`top`, `params`), then the PPA columns of the
    very netlist it wrote. Returns {"score": score.py's result, "ppa": the columns}. Raises PpaError (IllegalNetlist: the
    repaired netlist is electrically illegal; and score.ScoreError from the flow). The unit depth of the scored netlist must
    equal `ltp -noff` of the flow and its cell count the gate count: a mismatch means the two readings of the netlist differ
    and nothing is reported. `repaired_out`: also write the repaired netlist (structural Verilog, `Repair.write`).
    `input_drive`: the cell driving every primary input (the task's, `input_drive_of`; None: the pins' default).
    With `mapped` (the default) the columns also carry `mapped`: flow A1' on the canonical RTLIL of the same run (its
    `available` is false, with a reason, for a design the mapping cannot weigh; a `MappedDefect` raises)."""
    score = _score_module()
    lib, pins = open_library(liberty, pins)           # fail early, before the synthesis
    work = tempfile.mkdtemp(prefix="svgolf-ppa-")
    try:
        net, il = os.path.join(work, "netlist.v"), os.path.join(work, "canon.il")
        res = score.score(sources, top, params, yosys, repeat, gate=gate, netlist_out=net,
                          rtlil_out=il if mapped else None, flow=flow)
        with open(net, "rb") as fh:
            data = fh.read()
        if netlist_out:
            shutil.copyfile(net, netlist_out)
        a = analyze(data.decode(), lib, pins, input_drive=input_drive)
        if a.unit_depth != res["depth"] or a.scored_gates != res["num_gates"]:
            raise PpaError(f"the PPA reading of the scored netlist (depth {a.unit_depth}, {a.scored_gates} gates) differs "
                           f"from score.py's (ltp depth {res['depth']}, {res['num_gates']} gates)")
        if repaired_out:
            with open(repaired_out, "w") as fh:
                fh.write(a.repair["text"])
        cols = columns(a, pins, lib, sha256_bytes(data), with_path=with_path)
        if mapped:
            with open(il, "rb") as fh:
                if sha256_bytes(fh.read()) != res["rtlil_sha256"]:
                    raise PpaError("the canonical RTLIL the mapping reads is not the one the scored netlist came from")
            cols["mapped"] = mapped_block(il, top, data.decode(), lib, pins, yosys=yosys, with_path=with_path,
                                          netlist_out=mapped_netlist_out)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return {"score": res, "ppa": cols}


def _combined():
    """leaderboard/combined.py (the one definition of the ranked product), loaded by path."""
    import importlib.util
    path = os.path.join(os.path.dirname(HERE), "leaderboard", "combined.py")
    spec = importlib.util.spec_from_file_location("svgolf_combined_ppa", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def summary_line(res, pdk="sky130", latency=None):
    """The one stderr line after the JSON (a reader's convenience, never part of the result): the weighed area and
    delay of `res` (`main`'s result) on `pdk`'s columns; a clocked netlist (`sequential`) shows its period, and with
    `latency` (cycles) the ranked score, area x cycles x period; a combinational one area x delay. None when the
    columns carry no area or time."""
    p = res.get("ppa") or {}
    d = 5 if pdk == "asap7" else 4
    area, t, ai = p.get(f"area_um2_{pdk}"), p.get(f"delay_ps_{pdk}"), p.get(f"area_e{d}um2_{pdk}")
    if area is None or not isinstance(t, int) or not isinstance(ai, int):
        return None
    comb = _combined()
    name = f"ppa ({pdk} A0')"
    if p.get("sequential"):
        line = f"{name}: area {area} um^2, period {t} ps"
        if latency is not None:
            s = comb.um2ns(ai * latency * t, pdk)
            line += (f"; score: {area} um^2 x {latency} cycle{'' if latency == 1 else 's'} x {t} ps = {s:.2f} "
                     f"{comb.UNIT_ASCII}")
        return line
    return f"{name}: area {area} um^2, delay {t} ps; area x delay = {comb.um2ns(ai * t, pdk):.2f} {comb.UNIT_ASCII}"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="*")
    ap.add_argument("--top")
    ap.add_argument("--param", action="append")
    ap.add_argument("--task")
    ap.add_argument("--netlist-in", metavar="SCORED.v")
    ap.add_argument("--fetch-liberty", action="store_true")
    ap.add_argument("--liberty")
    ap.add_argument("--pdk", choices=sorted(PDKS), help="the library: sky130 (the default, the ranked columns) or asap7")
    ap.add_argument("--pins")
    ap.add_argument("--json")
    ap.add_argument("--netlist")
    ap.add_argument("--mapped-netlist", metavar="OUT")
    ap.add_argument("--repaired-netlist", metavar="OUT")
    ap.add_argument("--no-mapped", action="store_true")
    ap.add_argument("--path", action="store_true")
    ap.add_argument("--repeat", type=int, default=1)
    ap.add_argument("--yosys")
    ap.add_argument("--no-gate", action="store_true")
    ap.add_argument("--seq", action="store_true", help="the clocked flow (score.py --seq); implies --no-mapped")
    ap.add_argument("--input-drive", metavar="CELL", help="the cell driving every primary input (default: the task's "
                    "input_drive with --task, else the pins' default); one of the pins' timing.input_drive.allowed")
    ap.add_argument("--latency", type=int, metavar="L", help="with --seq (or --netlist-in of a clocked netlist): the "
                    "latency in cycles; the stderr summary line then shows the ranked score, area x L cycles x period")
    args = ap.parse_args(argv)
    if args.latency is not None and (not (args.seq or args.netlist_in) or args.latency < 1):
        ap.error("--latency L takes --seq (or --netlist-in) and L >= 1: the latency in cycles of a clocked design")

    try:
        pins = Pins(args.pins) if args.pins else Pins(pdk_paths(args.pdk or "sky130")[0])
        if args.pdk and pins.pdk != args.pdk:
            ap.error(f"--pins {args.pins} is a {pins.pdk} pins file, not {args.pdk}")
        if args.fetch_liberty:
            p = fetch_liberty(args.liberty, pins)
            print(json.dumps({"liberty": p, "sha256": pins.lib["sha256"]} if not pins.multi else
                             {"liberty": p, "sha256": set_sha256(pins.lib_files),
                              "files": {f["file"]: f["sha256"] for f in pins.lib_files}}, indent=2, sort_keys=True))
            return 0
        task = None
        if args.task:
            if HERE not in sys.path:
                sys.path.insert(0, HERE)
            import score
            try:
                task = score.load_task(args.task)
            except (OSError, ValueError) as e:
                raise PpaError(f"cannot read the task {args.task}: {e}")
        drive = input_drive_of(task, pins)
        if args.input_drive and args.input_drive != drive:
            if task is not None and "input_drive" in task:
                ap.error(f"--input-drive {args.input_drive} contradicts the task's input_drive {drive}")
            drive = check_input_drive(args.input_drive, pins, "--input-drive")
        if args.netlist_in:
            if args.sources:
                ap.error("--netlist-in takes no source files")
            if args.mapped_netlist:
                ap.error("--mapped-netlist needs a design (flow A1' maps the canonical RTLIL, not a scored netlist)")
            res = {"ppa": weigh_netlist_file(args.netlist_in, args.liberty, pins, args.path, args.repaired_netlist,
                                             input_drive=drive)}
        else:
            if not args.sources:
                ap.error("no source files (or --netlist-in)")
            if args.mapped_netlist and args.no_mapped:
                ap.error("--mapped-netlist contradicts --no-mapped")
            if HERE not in sys.path:
                sys.path.insert(0, HERE)
            import score
            if task is not None:
                top, params = score.task_scoring_point(task)
                params.update(score.parse_params(args.param))
                if args.top and args.top != top:
                    ap.error(f"--top {args.top} contradicts the task's top {top}")
            else:
                if not args.top:
                    ap.error("--top (or --task) is required")
                top, params = args.top, score.parse_params(args.param)
            try:
                res = score_and_weigh(args.sources, top, params, args.liberty, pins, args.yosys, args.repeat,
                                      gate=not args.no_gate, netlist_out=args.netlist, with_path=args.path,
                                      mapped=not (args.no_mapped or args.seq), mapped_netlist_out=args.mapped_netlist,
                                      flow="seq" if args.seq else "comb", repaired_out=args.repaired_netlist,
                                      input_drive=drive)
            except score.ScoreError as e:
                raise PpaError(f"the pinned flow failed: {e}")
    except PpaError as e:
        print(json.dumps({"error": str(e)}, indent=2))
        return 1
    text = json.dumps(res, indent=2, sort_keys=True)
    print(text)
    if args.json:
        with open(args.json, "w") as fh:
            fh.write(text + "\n")
    try:
        line = summary_line(res, pins.col, args.latency)
    except Exception as e:   # noqa: BLE001  (a reader's convenience: never a failure after the result is printed)
        line = f"ppa: no summary: {type(e).__name__}: {e}"
    if line:
        print(line, file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
