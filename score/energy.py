#!/usr/bin/env python3.12
"""svGolf ENERGY columns on sky130_fd_sc_hd: EXTRA, unranked, versioned fields beside the A0' columns of ppa.py (never GE).

  energy_activity_sky130_v1  fJ per operation, zero-delay toggle counts (every net toggles at most once per transition)
  energy_glitch_sky130_v1    fJ per operation, event-driven simulation with inertial NLDM delays (pulses shorter than a
                             gate's delay are swallowed): glitches counted
  leakage_sky130_v1          nW, the sum of cell_leakage_power (state-independent; the `when` tables are NOT used)
  clocked netlists ($_DFF_P_ = dfxtp_1): energy_cycle_sky130_v1, fJ per clock cycle = data toggles + flop clock pins (both
                             edges, every cycle) + a clock-tree estimate; per transaction = cycles x per cycle (--cycles)

Model (design/ppa/metrics.md section 2, the 10/30 spike design/ppa/spike/sky_measure.py): a toggle of a net costs
1/2 C V^2, C = fan-out pin capacitances + po_load per output bit (+ flop D pins), V = the liberty's nom_voltage; a toggle
of a cell output costs the mean over its internal_power groups of the rise_power or fall_power table at (worst input
transition, load). Transitions are the ranked STA's (ppa.analyze, both edges, the larger), delays the cell tables at them.
The netlist is the one the ranked score weighs (sky130_a0_v3): the A0' expansion (each `abc -g` gate one _1 cell) REPAIRED by
buffering (buffer trees, replicated tie cells; ppa.repair), its inputs driven by the task's input drive (`input_drive`, default
the pins'), legal (an illegal one raises IllegalNetlist: no energy for a rejected design). Every table is read inside its
grid (ppa.Table.at never extrapolates; the clock-pin power table neither).

Stimulus (pinned, uniform over every input bit): vector k of seed s = SHA-256("svgolf-energy/v1/<s>/<k>/<block>"). The
public development seed is "dev"; the OFFICIAL figures are the mean over OFFICIAL seeds derived from a salt
($SVGOLF_ENERGY_SALT; "public" if unset, and the result says which: only its sha256 is recorded). Toggle counts are
integers and every sum runs in a fixed order, so a result is bit-identical run to run (test_energy.py).

  python3.12 score/energy.py SOLUTION.sv --top TOP [--param N=16]      # the pinned comb flow, then its netlist
  python3.12 score/energy.py --netlist-in SCORED.v [--cycles C]        # an existing scored netlist (clocked or not)
  ... [--input-drive CELL]                                               # the inputs' driver (default: the pins' default)
"""
import argparse
import hashlib
import heapq
import json
import math
import os
import re
import sys
import tempfile
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import ppa  # noqa: E402

VERSION = "sky130_energy_v1"
TRANSITIONS, PAIRS, OFFICIAL = 1000, 100, 4     # zero-delay transitions, glitch-aware transitions, official seeds per run
CYCLES, LANES = 200, 64                         # clocked: cycles per trace, traces in parallel (bit lanes)
RESET_CYCLES = 2                                # clocked: a port named `rst` is asserted in the first cycles
FLOP, FLOP_CELL, CLK_BUF, CLK_FANOUT = "$_DFF_P_", "dfxtp_1", "clkbuf_1", 4
SALT_ENV = "SVGOLF_ENERGY_SALT"


def seeds(salt=None):
    salt = os.environ.get(SALT_ENV, "public") if salt is None else salt
    off = [hashlib.sha256(f"{salt}/{i}".encode()).hexdigest()[:16] for i in range(OFFICIAL)]
    return off, {"dev_seed": "dev", "official_seeds": OFFICIAL, "salted": salt != "public",
                 "salt_sha256": hashlib.sha256(salt.encode()).hexdigest()}


def lanes(bits, n, seed):
    """{bit: n-bit int}: bit k of the value of `bits[j]` is bit j of the SHA-256 stream of (seed, k)."""
    out, blocks = {b: 0 for b in bits}, (len(bits) + 255) // 256
    for k in range(n):
        x = int.from_bytes(b"".join(hashlib.sha256(f"svgolf-energy/v1/{seed}/{k}/{c}".encode()).digest()
                                    for c in range(blocks)), "little")
        for j, b in enumerate(bits):
            if x >> j & 1:
                out[b] |= 1 << k
    return out


def cell_group(lib, name):
    """The parsed liberty group of any cell (ppa.Cell admits combinational arcs only)."""
    text, start, depth = lib._text, lib._start[name], 0
    for m in ppa._BRACE_RE.finditer(text, text.index("{", start)):
        depth += {"{": 1, "}": -1}.get(m.group(0), 0)
        if depth == 0:
            return ppa._parse_group_text(text[start:m.end()])
    raise ppa.PpaError(f"liberty: unbalanced braces in cell {name}")


def pin_cap(lib, cell, pin):
    return float(next(p for p in cell_group(lib, cell).find("pin") if p.args[0] == pin).attrs["capacitance"])


def table1(g, x):
    """A 1-D liberty table (input-pin internal power) at x: linear interpolation inside its index, never extrapolated."""
    i1 = [float(v) for v in g.attrs["index_1"][0].split(",")]
    v = [float(t) for t in g.attrs["values"][0].split(",")]
    if not i1[0] <= x <= i1[-1]:
        raise ppa.TableRange(f"a power table read at {x:g} ns outside its index [{i1[0]:g}, {i1[-1]:g}] ns")
    k = max(0, min(len(i1) - 2, sum(1 for t in i1 if t <= x) - 1))
    return v[k] + (v[k + 1] - v[k]) * (x - i1[k]) / (i1[k + 1] - i1[k])


class Power:
    """Leakage (nW), output-pin internal energy (fJ per rise / fall at (transition, load)) and clock-pin energy per cell."""

    def __init__(self, lib):
        self.lib, self.cache = lib, {}
        self.vdd = float(re.search(r"nom_voltage\s*:\s*([\d.]+)", lib._text).group(1))

    def cell(self, name):
        if name not in self.cache:
            g = cell_group(self.lib, name)
            outs, clk = {}, None
            for p in g.find("pin"):
                ip = p.find("internal_power")
                if p.attrs.get("direction") == "output":
                    outs[p.args[0]] = ([ppa.Table(t.find("rise_power")[0], name) for t in ip],
                                       [ppa.Table(t.find("fall_power")[0], name) for t in ip])
                elif p.attrs.get("clock") == "true":
                    clk = (ip[0].find("rise_power")[0], ip[0].find("fall_power")[0], float(p.attrs["capacitance"]))
            self.cache[name] = (float(g.attrs.get("cell_leakage_power", 0.0)), outs, clk)
        return self.cache[name]

    def internal_fj(self, name, pin, slew, load):
        _, outs, _ = self.cell(name)
        rise, fall = outs.get(pin, ([], []))
        mean = lambda ts: sum(t.at(slew, load) for t in ts) / len(ts) if ts else 0.0  # noqa: E731
        return 1000 * mean(rise), 1000 * mean(fall)


class Model:
    """The REPAIRED A0' netlist the ranked score weighs (ppa.analyze, sky130_a0_v3: buffer trees and replicated tie cells,
    inputs driven by `input_drive` (the task's; None: the pins' default), legal or IllegalNetlist), its flops cut out (their Q
    nets become sources, their D pins loads), weighed per net."""

    def __init__(self, text, lib, pins, input_drive=None):
        a = ppa.analyze(text, lib, pins, input_drive=input_drive)
        self.flops, self.q, self.dnet, d, self.ties = a.flop_gates, a.q, a.dn, a.design, a.ties
        self.input_drive = a.input_drive
        clocks = {d.nl.resolve(f.pins["C"]) for f in self.flops}
        self.data_pi = [n for n in a.inputs if n not in clocks]
        self.d, self.pw, self.pins = d, Power(lib), pins
        flop = pins.prefix + FLOP_CELL
        # the STA's transitions (both edges, the larger), so that every table is read where the ranked weighing read it
        slew = {n: max(d.arr[(n, e)][1] for e in "rf" if (n, e) in d.arr) for n, _ in d.arr}
        self.delay, self.w = {}, {}
        v2 = 0.5 * self.pw.vdd ** 2 * 1000                      # pF * V^2 -> fJ
        for i in d.order:                                       # delays, then the per-toggle energies
            c = d.cells[i]
            ins = [n for n in d.ins[i].values() if n not in ("0", "1")]
            sin = max([slew.get(n, pins.pi_slew_ns) for n in ins] or [pins.pi_slew_ns])     # a constant cone has no arrival
            for op, onet in d.outs[i].items():
                load = d.load_pf(onet, pins.po_load_pf)        # flop D pins included (ppa.weigh_cells)
                arcs = [a for a in c.arcs[op] if d.ins[i][a.related] not in ("0", "1")]
                dr = max([a.tbl["cell_rise"].at(slew.get(d.ins[i][a.related], pins.pi_slew_ns), load) for a in arcs] or [0.0])
                df = max([a.tbl["cell_fall"].at(slew.get(d.ins[i][a.related], pins.pi_slew_ns), load) for a in arcs] or [0.0])
                self.delay[onet] = (dr, df)
                er, ef = self.pw.internal_fj(c.name, op, sin, load)
                self.w[onet] = (load * v2 + er, load * v2 + ef)
        for n in d.nl.pi:                                       # sources: the environment or a flop's Q drives them
            load = d.load_pf(n, pins.po_load_pf)
            er, ef = self.pw.internal_fj(flop, "Q", pins.pi_slew_ns, load) if n in self.q and load > 0 else (0.0, 0.0)
            self.w[n] = (load * v2 + er, load * v2 + ef)
        self.nets = sorted(self.w)

    def energy(self, rises, falls):
        return sum(rises.get(n, 0) * self.w[n][0] + falls.get(n, 0) * self.w[n][1] for n in self.nets)

    def leakage_nw(self):
        cells = [c.name for c in self.d.cells] + [self.pins.prefix + FLOP_CELL] * len(self.flops)
        cells += [self.pins.prefix + self.pins.tie_cell] * self.ties        # the repair's tie cells (one, or more)
        return sum(self.pw.cell(n)[0] for n in cells)

    def settle(self, values, mask):
        return ppa.simulate(self.d, values, mask)


def toggles(cur, nxt, mask, nets):
    r, f = {}, {}
    for n in nets:
        a, b = cur.get(n, 0), nxt.get(n, 0)
        r[n], f[n] = bin(b & ~a & mask).count("1"), bin(a & ~b & mask).count("1")
    return r, f


def glitch_toggles(m, v, pairs):
    """Inertial-delay event simulation of the first `pairs` transitions of the zero-delay values `v` (lane k -> k+1)."""
    d, rises, falls = m.d, defaultdict(int), defaultdict(int)
    fan = defaultdict(list)
    for i, ins in enumerate(d.ins):
        for n in set(ins.values()):
            fan[n].append(i)
    for k in range(pairs):
        val = {n: (v[n] >> k) & 1 for n in m.nets}
        val["0"], val["1"] = 0, 1
        q, pending, seq = [], {}, 0

        def evaluate(cells, t):
            nonlocal seq
            for i in sorted(set(cells)):
                env = {p: val[n] for p, n in d.ins[i].items()}
                for op, onet in d.outs[i].items():
                    y = eval(ppa._cell_fn(d.cells[i], op), {"__builtins__": {}}, {"v": env, "M": 1})
                    if onet in pending:
                        if y == val[onet]:
                            del pending[onet]            # a pulse shorter than the delay: swallowed
                    elif y != val[onet]:
                        seq += 1
                        pending[onet] = (y, seq)
                        heapq.heappush(q, (t + m.delay[onet][0 if y else 1], seq, onet))
        moved = []
        for n in d.nl.pi:
            y = (v[n] >> (k + 1)) & 1
            if y != val[n]:
                val[n] = y
                (rises if y else falls)[n] += 1
                moved += fan[n]
        evaluate(moved, 0.0)
        while q:
            t, s, onet = heapq.heappop(q)
            if pending.get(onet, (None, None))[1] != s:
                continue
            y = pending.pop(onet)[0]
            val[onet] = y
            (rises if y else falls)[onet] += 1
            evaluate(fan[onet], t)
        assert all(val[n] == (v[n] >> (k + 1)) & 1 for n in m.nets), "event simulation settled off the zero-delay values"
    return rises, falls


def comb_energy(m, seed):
    n = TRANSITIONS + 1
    mask = (1 << n) - 1
    v = m.settle(lanes(m.data_pi, n, seed), mask)
    lo, hi = {k: x & (mask >> 1) for k, x in v.items()}, {k: x >> 1 for k, x in v.items()}
    act = m.energy(*toggles(lo, hi, mask >> 1, m.nets)) / TRANSITIONS
    pm = (1 << PAIRS) - 1
    same = m.energy(*toggles({k: x & pm for k, x in v.items()}, {k: (x >> 1) & pm for k, x in v.items()}, pm, m.nets))
    gl = m.energy(*glitch_toggles(m, v, PAIRS))
    return {"activity_fj": act, "glitch_fj": gl / PAIRS, "glitch_factor": gl / same if same else 1.0}


def clock_fj(m):
    """Per cycle: every flop's CLK pin internal energy (rise + fall) and the clock net (both edges), with an estimated
    fan-out-4 tree of clkbuf_1 (ceil((F-1)/3) buffers, their input pins on the clock net, their internal energy)."""
    f = len(m.flops)
    if not f:
        return 0.0, 0.0, 0
    p, s = m.pins, m.pins.pi_slew_ns
    rise, fall, cap = m.pw.cell(p.prefix + FLOP_CELL)[2]
    pins_fj = f * 1000 * (table1(rise, s) + table1(fall, s))
    nbuf = math.ceil((f - 1) / (CLK_FANOUT - 1))
    bcap = pin_cap(m.pw.lib, p.prefix + CLK_BUF, "A")
    er, ef = m.pw.internal_fj(p.prefix + CLK_BUF, "X", s, CLK_FANOUT * cap)
    tree_fj = 2 * 0.5 * m.pw.vdd ** 2 * 1000 * (f * cap + nbuf * bcap) + nbuf * (er + ef)
    return pins_fj, tree_fj, nbuf


def clocked_energy(m, seed):
    """Fixed traces, LANES in parallel: random initial flops, `rst` asserted RESET_CYCLES cycles, then random inputs."""
    mask = (1 << LANES) - 1
    state = lanes(m.q, LANES, f"{seed}/init")
    prev, total, counted = None, 0.0, 0
    for t in range(CYCLES):
        ins = lanes(m.data_pi, LANES, f"{seed}/{t}")
        if "rst" in ins:
            ins["rst"] = mask if t < RESET_CYCLES else 0
        cur = m.settle({**ins, **state}, mask)
        if prev is not None and t > RESET_CYCLES:
            total += m.energy(*toggles(prev, cur, mask, m.nets))
            counted += LANES
        prev, state = cur, {q: cur.get(dn, 0) for q, dn in zip(m.q, m.dnet)}
    return {"data_fj": total / counted}


def measure(text, lib, pins, cycles=None, salt=None, input_drive=None):
    m = Model(text, lib, pins, input_drive)
    off, stim = seeds(salt)
    run = clocked_energy if m.flops else comb_energy
    per = {s: run(m, s) for s in ["dev"] + off}
    mean = lambda k: sum(per[s][k] for s in off) / len(off)  # noqa: E731
    r3 = lambda x: round(x, 3)  # noqa: E731
    out = {"energy_version": VERSION, "leakage_sky130_v1": r3(m.leakage_nw()), "vdd": m.pw.vdd,
           "per_seed": {s: {k: r3(x) for k, x in per[s].items()} for s in per},
           "stimulus": dict(stim, transitions=TRANSITIONS, glitch_pairs=PAIRS, cycles=CYCLES, lanes=LANES),
           "liberty_sha256": lib.sha256, "ppa_pins_sha256": pins.sha256, "input_drive": m.input_drive,
           "energy_script_sha256": ppa.sha256_file(os.path.abspath(__file__)),
           "netlist_sha256": ppa.sha256_bytes(text.encode())}
    if m.flops:
        pins_fj, tree_fj, nbuf = clock_fj(m)
        cyc = mean("data_fj") + pins_fj + tree_fj
        out.update({"energy_cycle_sky130_v1": r3(cyc), "flops": len(m.flops), "clock_pins_fj": r3(pins_fj),
                    "clock_tree_fj": r3(tree_fj), "clock_tree_buffers": nbuf})
        if cycles:
            out["energy_transaction_sky130_v1"] = {"cycles": cycles, "fj": r3(cycles * cyc)}
    else:
        out.update({"energy_activity_sky130_v1": r3(mean("activity_fj")),
                    "energy_glitch_sky130_v1": r3(mean("glitch_fj")), "glitch_factor": r3(mean("glitch_factor"))})
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="*")
    ap.add_argument("--top")
    ap.add_argument("--param", action="append", default=[])
    ap.add_argument("--netlist-in")
    ap.add_argument("--cycles", type=int)
    ap.add_argument("--liberty")
    ap.add_argument("--input-drive", metavar="CELL")
    a = ap.parse_args(argv)
    try:
        lib, pins = ppa.open_library(a.liberty)
        if a.netlist_in:
            text = open(a.netlist_in).read()
        else:
            import score
            path = os.path.join(tempfile.mkdtemp(prefix="svgolf-energy-"), "netlist.v")
            score.score(a.sources, a.top, score.parse_params(a.param), netlist_out=path)
            text = open(path).read()
        drive = ppa.check_input_drive(a.input_drive, pins, "--input-drive") if a.input_drive else None
        print(json.dumps(measure(text, lib, pins, a.cycles, input_drive=drive), indent=2, sort_keys=True))
    except ppa.PpaError as e:
        print(json.dumps({"error": str(e)}, indent=2))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
