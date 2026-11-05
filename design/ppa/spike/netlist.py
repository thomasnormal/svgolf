"""Parse the structural Verilog that Yosys `write_verilog -noattr -noexpr` emits
(the scored netlist: `\\$_AND_ _12_ (.A(x), .B(y), .Y(z));` instances, `assign`
of port vectors, no behavioral code) into a bit-level gate graph.

Nets are strings: scalar wires `_12_`, port bits `a[3]`, constants "0" / "1".
Works for the generic Yosys gate cells and for netlists mapped onto a liberty
cell library (`abc -liberty`): any `TYPE inst (.PIN(net), ...);`; which pins
are inputs/outputs is told by `outputs_of(type)` (default: Y for `$_X_` cells,
else decided by the liberty).
"""
import re
from collections import defaultdict

GENERIC_OUT = {"Y"}


class Gate:
    __slots__ = ("kind", "inst", "pins")

    def __init__(self, kind, inst, pins):
        self.kind, self.inst, self.pins = kind, inst, pins  # pins: {pin: net}


class Netlist:
    def __init__(self):
        self.name = None
        self.ports = []          # (name, dir, width)
        self.gates = []          # Gate objects (topologically unordered)
        self.alias = {}          # net -> net (from `assign`)
        self.pi = []             # primary input bits, port order, LSB first
        self.po = []             # (port, bit, net) after alias resolution

    # ------------------------------------------------------------------
    def resolve(self, net):
        seen = 0
        while net in self.alias:
            net = self.alias[net]
            seen += 1
            assert seen < 10000, "alias loop"
        return net


def _bits(expr, widths):
    """A Verilog net expression -> list of bit nets, MSB first."""
    expr = expr.strip()
    if expr.startswith("{") and expr.endswith("}"):
        out = []
        for part in _split_top(expr[1:-1]):
            out += _bits(part, widths)
        return out
    m = re.fullmatch(r"(\d+)'[bhd]([0-9a-fA-F_]+)", expr)
    if m:
        w = int(m.group(1))
        base = {"b": 2, "h": 16, "d": 10}[expr[expr.index("'") + 1]]
        v = int(m.group(2).replace("_", ""), base)
        return [str((v >> i) & 1) for i in reversed(range(w))]
    m = re.fullmatch(r"([^\s\[\]]+)\[(\d+)\]", expr)
    if m:
        return [f"{m.group(1)}[{int(m.group(2))}]"]
    m = re.fullmatch(r"([^\s\[\]]+)\[(\d+):(\d+)\]", expr)
    if m:
        hi, lo = int(m.group(2)), int(m.group(3))
        return [f"{m.group(1)}[{i}]" for i in range(hi, lo - 1, -1)]
    name = expr
    w = widths.get(name)
    if w is None:
        return [name]
    return [f"{name}[{i}]" for i in reversed(range(w))]


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


def parse(text, outputs_of=None):
    nl = Netlist()
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    m = re.search(r"module\s+(\S+?)\s*\(", text)
    nl.name = m.group(1)
    widths = {}
    for d in re.finditer(r"^\s*(input|output)\s*(?:\[(\d+):(\d+)\])?\s*(\S+);", text, re.M):
        w = 1 if d.group(2) is None else int(d.group(2)) - int(d.group(3)) + 1
        nl.ports.append((d.group(4), d.group(1), w))
        if d.group(2) is not None:
            widths[d.group(4)] = w
    for d in re.finditer(r"^\s*wire\s*\[(\d+):(\d+)\]\s*(\S+);", text, re.M):
        widths.setdefault(d.group(3), int(d.group(1)) - int(d.group(2)) + 1)
    for name, direction, w in nl.ports:
        if direction == "input":
            nl.pi += [f"{name}[{i}]" if name in widths else name for i in range(w)]
    for a in re.finditer(r"^\s*assign\s+(.+?)\s*=\s*(.+?);", text, re.M | re.S):
        lhs, rhs = _bits(a.group(1), widths), _bits(a.group(2), widths)
        assert len(lhs) == len(rhs), (a.group(0)[:80], len(lhs), len(rhs))
        for l, r in zip(lhs, rhs):
            nl.alias[l] = r
    inst_re = re.compile(r"^\s*(\\?\$?[\w$]+)\s+(\\?\S+)\s*\(\s*((?:\.\w+\([^)]*\)\s*,?\s*)+)\)\s*;", re.M)
    pin_re = re.compile(r"\.(\w+)\(([^)]*)\)")
    for g in inst_re.finditer(text):
        kind = g.group(1).lstrip("\\")
        if kind in ("module", "input", "output", "wire", "assign"):
            continue
        pins = {}
        for p in pin_re.finditer(g.group(3)):
            bits = _bits(p.group(2), widths)
            assert len(bits) == 1, (kind, p.group(0))
            pins[p.group(1)] = bits[0]
        nl.gates.append(Gate(kind, g.group(2), pins))
    for name, direction, w in nl.ports:
        if direction == "output":
            for i in range(w):
                net = f"{name}[{i}]" if name in widths else name
                nl.po.append((name, i, net))
    return nl


def load(path, outputs_of=None):
    with open(path) as fh:
        return parse(fh.read(), outputs_of)
