"""PPA spike engine: a gate graph over liberty cells, with
  * unit-depth (cross-check against Yosys `ltp`),
  * logical-effort delay (textbook table, unit-size gates, fan-out term),
  * NLDM static timing (rise/fall, slew propagation, worst-slew merge: OpenSTA's
    graph-based convention), no wire parasitics,
  * area / leakage from the library,
  * zero-delay bit-parallel simulation -> toggle counts -> switching energy
    (1/2 C V^2 per toggle, C = fan-out pin caps + external load) and liberty
    internal energy,
  * inertial-delay event simulation (glitch-aware toggle counts).
Everything is deterministic: no randomness here (vectors come from vectors.py),
dicts are insertion-ordered, ties in the event queue are broken by gate index.
"""
import heapq
from collections import defaultdict

import liberty as L
import netlist as N

# ---------------------------------------------------------------------------
# Scored (generic Yosys gate) netlist -> Nangate45 cells
# ---------------------------------------------------------------------------
GENERIC_TO_LIB = {
    # kind: (lib cell, {generic pin: lib pin}, generic out pin -> lib out pin)
    "$_AND_":  ("AND2_X1",  {"A": "A1", "B": "A2"}, "ZN"),
    "$_NAND_": ("NAND2_X1", {"A": "A1", "B": "A2"}, "ZN"),
    "$_OR_":   ("OR2_X1",   {"A": "A1", "B": "A2"}, "ZN"),
    "$_NOR_":  ("NOR2_X1",  {"A": "A1", "B": "A2"}, "ZN"),
    "$_XOR_":  ("XOR2_X1",  {"A": "A", "B": "B"},   "Z"),
    "$_XNOR_": ("XNOR2_X1", {"A": "A", "B": "B"},   "ZN"),
    "$_MUX_":  ("MUX2_X1",  {"A": "A", "B": "B", "S": "S"}, "Z"),
    "$_NOT_":  ("INV_X1",   {"A": "A"},             "ZN"),
}


def expand_generic(nl):
    """Rewrite the scored netlist's gates as Nangate45 cell instances.
    ANDNOT(A,B) = A & ~B = NOR2(~A, B) and ORNOT(A,B) = A | ~B = NAND2(~A, B):
    one INV_X1 plus NOR2_X1 / NAND2_X1 (the cheapest 2-cell realisation: 1.667 GE;
    the GE table prices them 1.333). Returns a new Netlist whose gate kinds are
    liberty cell names."""
    out = N.Netlist()
    out.name, out.ports, out.alias, out.pi, out.po = nl.name, nl.ports, nl.alias, nl.pi, nl.po
    for g in nl.gates:
        if g.kind in GENERIC_TO_LIB:
            cell, pm, zo = GENERIC_TO_LIB[g.kind]
            pins = {pm[p]: n for p, n in g.pins.items() if p in pm}
            pins[zo] = g.pins["Y"]
            out.gates.append(N.Gate(cell, g.inst, pins))
        elif g.kind in ("$_ANDNOT_", "$_ORNOT_"):
            t = g.inst + "_na"
            out.gates.append(N.Gate("INV_X1", g.inst + "_i", {"A": g.pins["A"], "ZN": t}))
            cell = "NOR2_X1" if g.kind == "$_ANDNOT_" else "NAND2_X1"
            out.gates.append(N.Gate(cell, g.inst, {"A1": t, "A2": g.pins["B"], "ZN": g.pins["Y"]}))
        else:
            raise ValueError(f"unsupported generic cell {g.kind}")
    return out


def generic_depth(nl):
    """Unit depth of the SCORED netlist (every gate 1): must equal Yosys `ltp -noff`."""
    drv = {}
    for g in nl.gates:
        drv[nl.resolve(g.pins["Y"])] = g
    memo = {}

    def depth(net):
        net = nl.resolve(net)
        if net in ("0", "1") or net not in drv:
            return 0
        if net in memo:
            return memo[net]
        g = drv[net]
        stack = [(net, g)]
        # iterative to avoid recursion limits on 1500-gate chains
        order = []
        seen = set()
        todo = [net]
        while todo:
            n = todo.pop()
            if n in memo or n in seen or n in ("0", "1") or n not in drv:
                continue
            seen.add(n)
            order.append(n)
            for p, x in drv[n].pins.items():
                if p != "Y":
                    todo.append(nl.resolve(x))
        for n in reversed(order):
            gg = drv[n]
            memo[n] = 1 + max([memo.get(nl.resolve(x), 0) for p, x in gg.pins.items() if p != "Y"] or [0])
        return memo[net]

    return max(depth(net) for _, _, net in nl.po)


# ---------------------------------------------------------------------------
# Design: gate graph over liberty cells
# ---------------------------------------------------------------------------
class Design:
    def __init__(self, nl, lib):
        self.nl, self.lib = nl, lib
        self.cells = []        # per gate: liberty Cell
        self.ins = []          # per gate: {pin: net}
        self.outs = []         # per gate: {pin: net}
        self.names = []
        self.driver = {}       # net -> (gate idx, out pin)
        for g in nl.gates:
            c = lib.cell(g.kind)
            ins = {p: nl.resolve(n) for p, n in g.pins.items() if p in c.inputs}
            outs = {p: n for p, n in g.pins.items() if p in c.outputs}
            idx = len(self.cells)
            self.cells.append(c)
            self.ins.append(ins)
            self.outs.append(outs)
            self.names.append(g.inst)
            for p, n in outs.items():
                self.driver[n] = (idx, p)
        self.fanout = defaultdict(list)   # net -> [(gate idx, pin)]
        for i, ins in enumerate(self.ins):
            for p, n in ins.items():
                self.fanout[n].append((i, p))
        self.po_count = defaultdict(int)  # net -> number of PO bits it drives
        self.po_nets = []
        for _, _, net in nl.po:
            r = nl.resolve(net)
            self.po_nets.append(r)
            self.po_count[r] += 1
        self.order = self._topo()

    def _topo(self):
        indeg = [0] * len(self.cells)
        succ = defaultdict(list)
        for i, ins in enumerate(self.ins):
            for n in set(ins.values()):
                if n in self.driver:
                    j = self.driver[n][0]
                    succ[j].append(i)
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
        assert len(order) == len(self.cells), "combinational loop"
        return order

    # -- area / leakage ---------------------------------------------------
    def area_um2(self):
        return sum(c.area for c in self.cells)

    def leakage_nw(self):
        return sum(c.leak for c in self.cells)

    def cell_counts(self):
        cnt = defaultdict(int)
        for c in self.cells:
            cnt[c.name] += 1
        return dict(sorted(cnt.items()))

    # -- loads ---------------------------------------------------------------
    def load_ff(self, net, po_load_ff):
        c = sum(self.cells[i].pin_cap[p] for i, p in self.fanout.get(net, ()))
        return c + po_load_ff * self.po_count.get(net, 0)

    # -- NLDM STA ---------------------------------------------------------------
    def sta_nldm(self, pi_slew_ns=0.01, po_load_ff=6.8):
        """Longest path with rise/fall arrivals and worst-slew merge. Returns
        (delay_ns, path [(net, edge, arrival_ns)], arr) where arr[(net, edge)] =
        (arrival, slew, pred) and each gate output's `dly` table is kept for
        the timed simulation (self.gate_delay)."""
        arr = {}
        for n in self.nl.pi:
            arr[(n, "r")] = (0.0, pi_slew_ns, None)
            arr[(n, "f")] = (0.0, pi_slew_ns, None)
        self.load_cache = {}
        self.gate_delay = {}   # (gate idx, out pin) -> (rise delay, fall delay, max input slew)
        for i in self.order:
            c = self.cells[i]
            for op, onet in self.outs[i].items():
                load = self.load_ff(onet, po_load_ff)
                self.load_cache[onet] = load
                dly = {"r": 0.0, "f": 0.0}
                in_slew = 0.0
                for e in "rf":
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
                            d = arc.tbl[dkey].at(s0, load)
                            so = arc.tbl[tkey].at(s0, load)
                            smax = max(smax, so)
                            in_slew = max(in_slew, s0)
                            dly[e] = max(dly[e], d)
                            if best is None or t0 + d > best[0]:
                                best = (t0 + d, (inet, ie))
                    if best is not None:
                        arr[(onet, e)] = (best[0], smax, best[1])
                self.gate_delay[(i, op)] = (dly["r"], dly["f"], in_slew)
        worst = None
        for n in self.po_nets:
            for e in "rf":
                a = arr.get((n, e))
                if a and (worst is None or a[0] > worst[0]):
                    worst = (a[0], (n, e))
        path = []
        if worst:
            cur = worst[1]
            while cur is not None:
                a = arr[cur]
                path.append((cur[0], cur[1], a[0]))
                cur = a[2]
            path.reverse()
        return (worst[0] if worst else 0.0), path, arr

    # -- logical-effort STA (unit-size gates, textbook table) ---------------------
    def sta_le(self, po_load=4.0):
        """Delay in tau. Gate delay = p + C_load / C_inv (every gate is the
        unit-drive version of its type), C_load = sum of fan-out input caps +
        po_load per primary-output bit; no wire. Input cap and parasitic delay
        from LE_TABLE (Sutherland-Sproull-Harris, 'Logical Effort')."""
        at = {n: 0.0 for n in self.nl.pi}
        at["0"] = at["1"] = 0.0
        pred = {}
        for i in self.order:
            kind = LE_KIND[self.cells[i].name]
            p = LE_TABLE[kind][0]
            for op, onet in self.outs[i].items():
                load = po_load * self.po_count.get(onet, 0)
                for j, pin in self.fanout.get(onet, ()):
                    load += LE_TABLE[LE_KIND[self.cells[j].name]][1].get(pin, LE_TABLE[LE_KIND[self.cells[j].name]][1]["*"])
                tin = max(at.get(n, 0.0) for n in self.ins[i].values())
                at[onet] = tin + p + load
        return max(at[n] for n in self.po_nets)

    def unit_depth(self):
        lv = {}
        for i in self.order:
            l = 1 + max([lv.get(n, 0) for n in self.ins[i].values()] or [0])
            for onet in self.outs[i].values():
                lv[onet] = l
        return max(lv.get(n, 0) for n in self.po_nets)


# Textbook logical effort (unit-drive gates): kind -> (parasitic delay p in tau,
# {input pin: input capacitance in units of the unit inverter's input cap}).
# NAND2 g=4/3 p=2, NOR2 g=5/3 p=2, INV g=1 p=1 (Sutherland, Sproull, Harris,
# Logical Effort, 1999, Table 1.1); AND2/OR2 = NAND2/NOR2 + unit INV (p = 3 + 1 =
# 4, derived in README); XOR2/XNOR2 g=4 p=4 and MUX2 g=2 p=4 (the book's static
# CMOS figures for the non-complementary-input cell; Weste-Harris Table 4.x).
LE_TABLE = {
    "INV":   (1.0, {"*": 1.0}),
    "NAND2": (2.0, {"*": 4.0 / 3.0}),
    "NOR2":  (2.0, {"*": 5.0 / 3.0}),
    "AND2":  (4.0, {"*": 4.0 / 3.0}),
    "OR2":   (4.0, {"*": 5.0 / 3.0}),
    "XOR2":  (4.0, {"*": 4.0}),
    "XNOR2": (4.0, {"*": 4.0}),
    "MUX2":  (4.0, {"A": 2.0, "B": 2.0, "S": 4.0, "*": 2.0}),
}
LE_KIND = {"INV_X1": "INV", "NAND2_X1": "NAND2", "NOR2_X1": "NOR2", "AND2_X1": "AND2",
           "OR2_X1": "OR2", "XOR2_X1": "XOR2", "XNOR2_X1": "XNOR2", "MUX2_X1": "MUX2"}


# ---------------------------------------------------------------------------
# Simulation
# ---------------------------------------------------------------------------
class Sim:
    """Zero-delay bit-parallel simulation: every net is a Python int whose bit k
    is its value under input vector k."""

    def __init__(self, design):
        self.d = design
        self.fn = []
        for i, c in enumerate(design.cells):
            self.fn.append({op: compile(L.compile_function(c.function[op]), "<fn>", "eval")
                            for op in design.outs[i]})

    def run(self, pi_values, nvec):
        """pi_values: {pi bit net: int bitvector}. Returns {net: bitvector}."""
        mask = (1 << nvec) - 1
        v = dict(pi_values)
        v["0"], v["1"] = 0, mask
        d = self.d
        for i in d.order:
            env = {p: v[n] for p, n in d.ins[i].items()}
            g = {"v": env, "M": mask}
            for op, onet in d.outs[i].items():
                v[onet] = eval(self.fn[i][op], g)
        return v


def toggle_counts(v, nets, nvec):
    """For each net: (rises, falls) summed over the nvec-1 consecutive vector pairs."""
    m = (1 << (nvec - 1)) - 1
    out = {}
    for n in nets:
        x = v[n]
        a, b = x & m, x >> 1
        out[n] = (bin(b & ~a & m).count("1"), bin(a & ~b & m).count("1"))
    return out


def timed_toggle_counts(design, v, pi_nets, nvec, npairs, t_scale=1.0):
    """Glitch-aware toggle counts by event-driven simulation with inertial delays
    (rise/fall delay per gate output from sta_nldm), for the first `npairs`
    consecutive vector pairs of the zero-delay result `v`. Returns
    ({net: (rises, falls)}, glitch-free comparison {net: (rises, falls)} on the same
    pairs). Asserts that the settled values equal the zero-delay values."""
    d = design
    cells = d.cells
    funcs = []
    for i, c in enumerate(cells):
        funcs.append([(op, onet, compile(L.compile_function(c.function[op]), "<fn>", "eval"))
                      for op, onet in d.outs[i].items()])
    delay = {}
    for i in range(len(cells)):
        for op, onet in d.outs[i].items():
            dr, df, _ = d.gate_delay[(i, op)]
            delay[onet] = (dr * t_scale, df * t_scale)
    nets = set(v) - {"0", "1"}
    rises, falls = defaultdict(int), defaultdict(int)
    zr, zf = defaultdict(int), defaultdict(int)
    fan = {n: sorted({i for i, _ in d.fanout.get(n, ())}) for n in nets}
    for k in range(npairs):
        val = {n: (v[n] >> k) & 1 for n in nets}
        val["0"], val["1"] = 0, 1
        newv = {n: (v[n] >> (k + 1)) & 1 for n in nets}
        for n in nets:
            if val[n] != newv[n]:
                if newv[n]:
                    zr[n] += 1
                else:
                    zf[n] += 1
        pending = {}   # net -> (time, value, seq) ; one pending event per net (inertial)
        q = []
        seq = 0
        for n in pi_nets:
            if val[n] != newv[n]:
                val[n] = newv[n]
                if newv[n]:
                    rises[n] += 1
                else:
                    falls[n] += 1
        affected = set()
        for n in pi_nets:
            affected.update(fan.get(n, ()))
        t_now = 0.0
        work = sorted(affected)
        def evaluate(work, t_now):
            nonlocal seq
            for i in work:
                env = {p: val[n] for p, n in d.ins[i].items()}
                g = {"v": env, "M": 1}
                for op, onet, code in funcs[i]:
                    y = eval(code, g)
                    pend = pending.get(onet)
                    if pend is not None:
                        if y == val[onet]:
                            pending[onet] = None   # pulse swallowed
                        # else: same value as pending event, keep it
                    elif y != val[onet]:
                        dr, df = delay[onet]
                        seq += 1
                        t = t_now + (dr if y else df)
                        pending[onet] = (t, y, seq)
                        heapq.heappush(q, (t, seq, onet))
        evaluate(work, 0.0)
        while q:
            t, s, onet = heapq.heappop(q)
            pend = pending.get(onet)
            if pend is None or pend[2] != s:
                continue
            pending[onet] = None
            y = pend[1]
            val[onet] = y
            if y:
                rises[onet] += 1
            else:
                falls[onet] += 1
            evaluate(fan.get(onet, ()), t)
        for n in nets:
            assert val[n] == newv[n], f"timed sim settled wrong on {n} (pair {k})"
    out = {n: (rises[n], falls[n]) for n in nets}
    zero = {n: (zr[n], zf[n]) for n in nets}
    return out, zero
