"""A small Liberty (.lib) reader: just enough for NLDM delay, pin capacitance,
area, leakage, internal power and boolean functions. Standard library only.

  lib = Liberty.load(path)
  lib.cell("NAND2_X1").area            # um^2
  lib.cell("NAND2_X1").pin_cap["A1"]   # fF
  lib.cell("NAND2_X1").arcs            # list of Arc (related pin -> output pin)
  eval_function("!(A1 & A2)", {"A1": 1, "A2": 0})   # boolean functions (ints / big ints)

Units are those of the library (Nangate45: ns, fF, nW; internal power is a
table of energy per output transition in the library's own, unlabelled unit,
read here as fJ -- see README.md, "Power", for the sanity check).
"""
import bisect
import re

_TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][\w.\[\]$]*|-?[\d.]+(?:[eE][-+]?\d+)?|[{}():;,]')


class Group:
    __slots__ = ("kind", "args", "attrs", "children")

    def __init__(self, kind, args):
        self.kind, self.args, self.attrs, self.children = kind, args, {}, []

    def find(self, kind):
        return [c for c in self.children if c.kind == kind]


def _strip(text):
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"\\\s*\n", " ", text)
    return text


def parse(text):
    toks = _TOKEN.findall(_strip(text))
    pos = 0
    n = len(toks)

    def unq(t):
        return t[1:-1] if t.startswith('"') else t

    def group_body(g):
        nonlocal pos
        while pos < n and toks[pos] != "}":
            name = toks[pos]
            pos += 1
            t = toks[pos]
            if t == ":":
                pos += 1
                val = []
                while toks[pos] != ";":
                    val.append(unq(toks[pos]))
                    pos += 1
                pos += 1
                g.attrs[name] = val[0] if len(val) == 1 else val
            elif t == "(":
                pos += 1
                args = []
                while toks[pos] != ")":
                    if toks[pos] != ",":
                        args.append(unq(toks[pos]))
                    pos += 1
                pos += 1
                if pos < n and toks[pos] == "{":
                    pos += 1
                    c = Group(name, args)
                    group_body(c)
                    pos += 1  # }
                    g.children.append(c)
                else:
                    if toks[pos] == ";":
                        pos += 1
                    g.attrs[name] = args
            else:
                pos += 1

    root = Group("root", [])
    # top-level: library ( name ) { ... }
    name = toks[pos]; pos += 1
    assert toks[pos] == "("
    pos += 1
    args = []
    while toks[pos] != ")":
        if toks[pos] != ",":
            args.append(unq(toks[pos]))
        pos += 1
    pos += 2  # ) {
    lib = Group(name, args)
    group_body(lib)
    return lib


class Table:
    """A 2-D NLDM table (index_1 = input transition, index_2 = output load)."""
    __slots__ = ("i1", "i2", "v")

    def __init__(self, g):
        self.i1 = [float(x) for x in g.attrs["index_1"][0].split(",")]
        self.i2 = [float(x) for x in g.attrs["index_2"][0].split(",")]
        self.v = [[float(x) for x in row.split(",")] for row in g.attrs["values"]]

    def at(self, x1, x2):
        """Bilinear interpolation, linear extrapolation at the ends (what STA tools do)."""
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


class Arc:
    """A timing arc related_pin -> out pin: delay and transition tables per output edge."""
    def __init__(self, g):
        self.related = g.attrs["related_pin"]
        self.sense = g.attrs.get("timing_sense", "non_unate")
        self.when = g.attrs.get("when")
        self.tbl = {}
        for k in ("cell_rise", "cell_fall", "rise_transition", "fall_transition"):
            for c in g.find(k):
                self.tbl[k] = Table(c)


class Cell:
    def __init__(self, g):
        self.name = g.args[0]
        self.area = float(g.attrs["area"])
        self.leak = float(g.attrs.get("cell_leakage_power", 0.0))
        self.pin_cap, self.inputs, self.outputs = {}, [], []
        self.function, self.arcs = {}, {}
        self.power = {}  # out pin -> {"rise_power"/"fall_power": [Table, ...]}
        self.is_seq = bool(g.find("ff") or g.find("latch"))
        for p in g.find("pin"):
            pn = p.args[0]
            if p.attrs.get("direction") == "input":
                self.inputs.append(pn)
                self.pin_cap[pn] = float(p.attrs.get("capacitance", 0.0))
            elif p.attrs.get("direction") == "output":
                self.outputs.append(pn)
                self.function[pn] = p.attrs.get("function")
                self.arcs[pn] = [Arc(t) for t in p.find("timing")]
                pw = {"rise_power": [], "fall_power": []}
                for ip in p.find("internal_power"):
                    for k in pw:
                        for c in ip.find(k):
                            pw[k].append(Table(c))
                self.power[pn] = pw


class Liberty:
    def __init__(self, g):
        self.group = g
        self.name = g.args[0]
        self.attrs = g.attrs
        self._cells = {c.args[0]: c for c in g.find("cell")}
        self._cache = {}

    @classmethod
    def load(cls, path):
        with open(path) as fh:
            return cls(parse(fh.read()))

    def cell(self, name):
        if name not in self._cache:
            self._cache[name] = Cell(self._cells[name])
        return self._cache[name]

    def has(self, name):
        return name in self._cells


_FTOK = re.compile(r"[A-Za-z_]\w*|[!&|^()*+']|\s+")


def compile_function(expr):
    """Liberty boolean function -> a Python expression over a dict `v` of ints
    (Python big ints are used as bit-parallel vectors: `~` is done with a mask `M`)."""
    toks = [t for t in _FTOK.findall(expr) if not t.isspace()]
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def parse_or():
        nonlocal pos
        l = parse_xor()
        while peek() in ("|", "+"):
            pos += 1
            l = f"({l} | {parse_xor()})"
        return l

    def parse_xor():
        nonlocal pos
        l = parse_and()
        while peek() == "^":
            pos += 1
            l = f"({l} ^ {parse_and()})"
        return l

    def parse_and():
        nonlocal pos
        l = parse_not()
        while peek() in ("&", "*"):
            pos += 1
            l = f"({l} & {parse_not()})"
        return l

    def parse_not():
        nonlocal pos
        if peek() == "!":
            pos += 1
            return f"(M ^ {parse_not()})"
        a = parse_atom()
        while peek() == "'":
            pos += 1
            a = f"(M ^ {a})"
        return a

    def parse_atom():
        nonlocal pos
        t = peek()
        pos += 1
        if t == "(":
            e = parse_or()
            assert peek() == ")"
            pos += 1
            return e
        return f"v[{t!r}]"

    out = parse_or()
    assert pos == len(toks), (expr, toks[pos:])
    return out


def eval_function(expr, v, mask=1):
    return eval(compile_function(expr), {"v": v, "M": mask})
