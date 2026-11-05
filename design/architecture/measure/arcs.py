"""Bit-level combinational dependency analysis over pyslang's elaborated AST (WS4 X8; untrusted, a measurement tool).

For one module instance body it builds the module's OWN combinational graph at bit precision: a node per bit of every
variable, net and port, an edge `w <- r` when a continuous assign, a combinational process (`always_comb`, `always @*`,
`always @(a or b)`, `always_latch`) or a net initializer can make bit `w` depend on bit `r` within the time slot.
Edge processes (an event control with an edge) and `initial` blocks contribute nothing: their writes are state.

Child instances enter the parent's graph only through their ARC SUMMARY: for every output-port bit, the input-port bits
it depends on combinationally. The summary is computed bottom-up from the child's own graph and ITS children's
summaries, and is then COARSENED at the child's interface to one of three granularities:

    port   an output port depends on an input port if any bit of one depends on any bit of the other (all-to-all)
    field  the same per leaf field of a struct-typed port (arrays of structs: per element and field); other ports whole
    bit    exact

The parent's own logic is always bit-precise, so the granularity changes ONLY the child arcs. Every module's graph is
then searched for strongly connected components (a nontrivial SCC is a combinational cycle of the analysed graph).

Precision of the abstract evaluation (over-approximation everywhere; every rule below adds dependencies, never drops):
  bitwise ops and `?:` per bit (plus the whole condition); `+`, `-`, `*`, unary minus: bit i <- operand bits 0..i;
  constant shifts move bits; comparisons, reductions, logical ops, `/`, `%`, `**`, unknown system calls: all <- all;
  constant selects / member accesses slice; dynamic selects: every candidate element plus the index; concatenation,
  replication and assignment patterns positional; procedural code is executed abstractly with a per-variable
  environment (blocking reads see earlier writes in the same activation), control dependencies of every enclosing
  `if`/`case`/loop condition, a merge at every join (a bit written on one path only keeps a dependency on itself: a
  latch); `for` loops with constant headers are unrolled, other loops iterate to a fixpoint; `break`/`continue`/`return`
  make every later write depend on their condition. User functions are analysed per call with their formals as
  placeholders. Anything not modelled falls back to "every result bit depends on every bit the expression reads".
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402

ps = slang_env.pyslang()
from pyslang.ast import (SymbolKind, StatementKind, ExpressionKind, VisitAction, ArgumentDirection,  # noqa: E402
                         BinaryOperator as BO, UnaryOperator as UO, ProceduralBlockKind as PK,
                         TimingControlKind as TK, EdgeKind, RangeSelectionKind as RS,
                         CaseStatementCondition as CaseCond, EvalContext)

GRANULARITIES = ("module", "port", "field", "bit")
MAX_UNROLL = 4096


def iter_bits(m):
    while m:
        low = m & -m
        yield low.bit_length() - 1
        m ^= low


def cv_int(cv):
    try:
        if cv is None:
            return None
        v = cv.value if hasattr(cv, "value") else cv
        hu = getattr(v, "hasUnknown", False)
        if callable(hu):
            hu = hu()
        if hu:
            return None
        r = int(v)
        if getattr(v, "isSigned", False) and getattr(v, "bitWidth", 0) and r >= (1 << (int(v.bitWidth) - 1)):
            r -= 1 << int(v.bitWidth)
        return r
    except Exception:  # noqa: BLE001
        return None


def tw(t):
    """Bit width of a type in this analysis' flat layout (packed: bitWidth; unpacked: bitstream width)."""
    try:
        if t.isIntegral:
            return int(t.bitWidth)
        b = t.bitstreamWidth
        b = b() if callable(b) else b
        return int(b) if b else 1
    except Exception:  # noqa: BLE001
        return 1


def canon(t):
    try:
        return t.canonicalType
    except Exception:  # noqa: BLE001
        return t


def elem_info(t):
    """(range, element width) for indexing a value of type t, or (None, 1)."""
    ct = canon(t)
    rng = getattr(ct, "range", None)
    et = getattr(ct, "elementType", None)
    if rng is not None and et is not None:
        return rng, tw(et)
    try:
        if ct.hasFixedRange:
            return ct.fixedRange, 1
    except Exception:  # noqa: BLE001
        pass
    return None, 1


def translate(rng, idx):
    """Zero-based position (from the LSB end of the flat layout) of index `idx` in range `rng`, or None if outside."""
    lo, hi = min(rng.left, rng.right), max(rng.left, rng.right)
    if idx < lo or idx > hi:
        return None
    return (idx - rng.right) if rng.left >= rng.right else (rng.right - idx)


def struct_fields(t):
    ct = canon(t)
    name = type(ct).__name__
    if name in ("PackedStructType", "UnpackedStructType", "PackedUnionType", "UnpackedUnionType"):
        return [f for f in ct if f.kind == SymbolKind.Field]
    return None


def field_atoms(t, base=0):
    """Leaf atoms (lo, width) of a value of type t at field granularity."""
    fs = struct_fields(t)
    if fs is not None and type(canon(t)).__name__ in ("PackedStructType", "UnpackedStructType"):
        out = []
        for f in fs:
            out += field_atoms(f.type, base + int(f.bitOffset))
        return out or [(base, tw(t))]
    ct = canon(t)
    rng, ew = elem_info(t)
    et = getattr(ct, "elementType", None)
    if rng is not None and et is not None and struct_fields(et) is not None:
        out = []
        for k in range(rng.width if not callable(rng.width) else rng.width()):
            out += field_atoms(et, base + k * ew)
        return out
    return [(base, tw(t))]


class Unsupported(Exception):
    pass


class State:
    __slots__ = ("env", "consts", "ctrl", "extra", "ret", "brk")

    def __init__(self, env=None, consts=None, ctrl=0):
        self.env = dict(env or {})
        self.consts = dict(consts or {})
        self.ctrl = ctrl
        self.extra = 0
        self.ret = None
        self.brk = 0

    def fork(self):
        s = State(self.env, self.consts, self.ctrl)
        s.extra, s.ret, s.brk = self.extra, self.ret, self.brk
        return s


class Module:
    """The analysis of one elaborated instance body."""

    def __init__(self, inst, summaries, stats, mode="lrm4"):
        # mode: "lrm4"  every case without a default keeps a no-match path (an x/z selector matches nothing, so
        #               the written variables hold: LRM 12.5);
        #       "2state" that path is dropped when the constant items cover every 2-state selector value;
        #       "yosys" additionally drops it for `unique`/`priority` case (Yosys reads them as full_case).
        #       "nofold" as lrm4 but with NO parameter folding (`P & x` keeps x's dependency when P = 0, an `if (P)`
        #               runs both arms): what an arc summary stated for EVERY parameter value has to carry.
        self.fold = (mode != "nofold")
        self.mode = "lrm4" if mode == "nofold" else mode
        self.inst = inst
        self.body = inst.body
        self.summaries = summaries      # callable(child_inst, gran) -> Summary
        self.stats = stats
        self.base = {}                  # symbol key -> (first node id, width, type)
        self.names = []                 # node id -> (signal label, bit)
        self.atoms_field = {}           # symbol key -> list of (lo, width)
        self.edges = {}                 # node -> mask (own logic)
        self.child_edges = {g: {} for g in GRANULARITIES}
        self.fn_cache = {}
        self.fn_stack = []
        self.child_ports = []           # (instance label, port, direction, key)
        self.fallbacks = 0
        self._ctx = None
        self.loop_keys = set()          # for-header loop variables: block-local, never committed
        self.writer = {}                # node -> id of the combinational process (assign / comb block) writing it
        self.nproc = 0

    # ------------------------------------------------------------------ nodes
    def key(self, sym):
        return sym.hierarchicalPath or ("%s@%d" % (sym.name, sym.location.offset))

    def nodes_of(self, key, width, label, typ=None):
        b = self.base.get(key)
        if b is None:
            first = len(self.names)
            for i in range(width):
                self.names.append((label, i))
            self.base[key] = (first, width, typ)
            if typ is not None:
                self.atoms_field[key] = field_atoms(typ)
            b = self.base[key]
        return b

    def sym_nodes(self, sym):
        k = self.key(sym)
        if k in self.base:
            return self.base[k]
        t = sym.type
        rel = k
        top = self.body.hierarchicalPath
        if top and rel.startswith(top + "."):
            rel = rel[len(top) + 1:]
        return self.nodes_of(k, tw(t), rel, t)

    def own(self, sym):
        first, w, _ = self.sym_nodes(sym)
        return [1 << (first + i) for i in range(w)]

    # ------------------------------------------------------------------ reading
    def read_sym(self, sym, st):
        k = self.key(sym)
        if sym.kind in (SymbolKind.Parameter, SymbolKind.EnumValue, SymbolKind.Specparam):
            return [0] * tw(sym.type)
        if k in st.consts:
            return [0] * tw(sym.type)
        own = self.own(sym)
        v = st.env.get(k)
        if v is None:
            return own
        return [own[i] if x is None else x for i, x in enumerate(v)]

    def all_reads(self, e, st):
        syms = []

        def v(n):
            kk = getattr(n, "kind", None)
            if kk in (ExpressionKind.NamedValue, ExpressionKind.HierarchicalValue):
                syms.append(n.symbol)
            return VisitAction.Advance
        e.visit(v)
        m = 0
        for s in syms:
            if s.kind in (SymbolKind.Variable, SymbolKind.Net, SymbolKind.FormalArgument, SymbolKind.Port,
                          SymbolKind.Field):
                for x in self.read_sym(s, st):
                    m |= x
        return m

    def conservative(self, e, st, width=None):
        self.fallbacks += 1
        self.stats["fallback_kinds"][str(e.kind).split(".")[-1]] = \
            self.stats["fallback_kinds"].get(str(e.kind).split(".")[-1], 0) + 1
        m = self.all_reads(e, st)
        return [m] * (width if width is not None else tw(e.type))

    def cint(self, e, st):
        c = getattr(e, "constant", None)
        if c is not None:
            r = cv_int(c)
            if r is not None:
                return r
        k = e.kind
        if k == ExpressionKind.IntegerLiteral:
            return cv_int(e.value)
        if k == ExpressionKind.NamedValue:
            s = e.symbol
            kk = self.key(s)
            if kk in st.consts:
                return st.consts[kk]
            if s.kind in (SymbolKind.Parameter, SymbolKind.EnumValue):
                return cv_int(s.value)
            return None
        if k == ExpressionKind.Conversion:
            return self.cint(e.operand, st)
        if k == ExpressionKind.BinaryOp:
            a, b = self.cint(e.left, st), self.cint(e.right, st)
            if a is None or b is None:
                return None
            op = e.op
            try:
                return {BO.Add: lambda: a + b, BO.Subtract: lambda: a - b, BO.Multiply: lambda: a * b,
                        BO.Divide: lambda: int(a / b) if b else None, BO.Mod: lambda: (abs(a) % abs(b)) * (1 if a >= 0 else -1) if b else None,
                        BO.LogicalShiftLeft: lambda: a << b, BO.LogicalShiftRight: lambda: a >> b,
                        BO.ArithmeticShiftLeft: lambda: a << b, BO.ArithmeticShiftRight: lambda: a >> b,
                        BO.LessThan: lambda: int(a < b), BO.LessThanEqual: lambda: int(a <= b),
                        BO.GreaterThan: lambda: int(a > b), BO.GreaterThanEqual: lambda: int(a >= b),
                        BO.Equality: lambda: int(a == b), BO.Inequality: lambda: int(a != b),
                        BO.BinaryAnd: lambda: a & b, BO.BinaryOr: lambda: a | b, BO.BinaryXor: lambda: a ^ b,
                        BO.LogicalAnd: lambda: int(bool(a) and bool(b)), BO.LogicalOr: lambda: int(bool(a) or bool(b)),
                        BO.Power: lambda: a ** b if 0 <= b < 64 else None}.get(op, lambda: None)()
            except Exception:  # noqa: BLE001
                return None
        if k == ExpressionKind.UnaryOp:
            a = self.cint(e.operand, st)
            if a is None:
                return None
            return {UO.Minus: -a, UO.Plus: a, UO.LogicalNot: int(not a)}.get(e.op)
        if k in (ExpressionKind.MemberAccess, ExpressionKind.ElementSelect, ExpressionKind.RangeSelect,
                 ExpressionKind.Call):
            return self.eval_pure(e)
        return None

    def eval_pure(self, e):
        """slang's own constant evaluation of an expression that reads no variable, net or loop variable
        (a member of a struct-valued parameter, `$clog2(P)`, a constant function call)."""
        impure = []

        def v(n):
            if getattr(n, "kind", None) in (ExpressionKind.NamedValue, ExpressionKind.HierarchicalValue):
                if n.symbol.kind not in (SymbolKind.Parameter, SymbolKind.EnumValue, SymbolKind.Specparam):
                    impure.append(n)
            return VisitAction.Advance
        e.visit(v)
        if impure:
            return None
        try:
            if self._ctx is None:
                self._ctx = EvalContext(self.body)
            return cv_int(e.eval(self._ctx))
        except Exception:  # noqa: BLE001
            return None

    def const_bits(self, e, st, w):
        """Per-bit 0/1 if e is a fully known constant (parameters folded), else None."""
        if not self.fold:
            return None
        v = None
        c = getattr(e, "constant", None)
        if c is not None:
            v = cv_int(c)
        if v is None:
            v = self.cint(e, st)
        if v is None:
            return None
        v &= (1 << w) - 1 if w > 0 else 0
        return [(v >> i) & 1 for i in range(w)]

    def const_truth(self, e, st):
        if not self.fold:
            return None
        c = getattr(e, "constant", None)
        v = cv_int(c) if c is not None else None
        if v is None:
            v = self.cint(e, st)
        return None if v is None else bool(v)

    # ------------------------------------------------------------------ expressions
    def ev(self, e, st):
        k = e.kind
        w = tw(e.type) if e.type is not None else 1
        if k in (ExpressionKind.IntegerLiteral, ExpressionKind.RealLiteral, ExpressionKind.TimeLiteral,
                 ExpressionKind.UnbasedUnsizedIntegerLiteral, ExpressionKind.NullLiteral,
                 ExpressionKind.StringLiteral, ExpressionKind.EmptyArgument, ExpressionKind.TypeReference,
                 ExpressionKind.DataType):
            return [0] * w
        c = getattr(e, "constant", None)
        if c is not None and k not in (ExpressionKind.NamedValue,):
            return [0] * w
        if k in (ExpressionKind.NamedValue, ExpressionKind.HierarchicalValue):
            s = e.symbol
            if s.kind in (SymbolKind.Variable, SymbolKind.Net, SymbolKind.FormalArgument, SymbolKind.Port):
                return self.fit(self.read_sym(s, st), w)
            return [0] * w
        if k == ExpressionKind.Conversion:
            v = self.ev(e.operand, st)
            if len(v) >= w:
                return v[:w]
            signed = False
            try:
                signed = bool(e.operand.type.isSigned)
            except Exception:  # noqa: BLE001
                pass
            fill = v[-1] if (signed and v) else 0
            return v + [fill] * (w - len(v))
        if k == ExpressionKind.ElementSelect:
            return self.ev_select(e, st, w)
        if k == ExpressionKind.RangeSelect:
            return self.ev_range(e, st, w)
        if k == ExpressionKind.MemberAccess:
            base = self.ev(e.value, st)
            m = e.member
            if m.kind == SymbolKind.Field:
                off = int(m.bitOffset)
                return self.fit(base[off:off + w], w)
            return self.conservative(e, st, w)
        if k == ExpressionKind.Concatenation:
            out = []
            for op in reversed(list(e.operands)):
                out += self.ev(op, st)
            return self.fit(out, w)
        if k == ExpressionKind.Replication:
            n = self.cint(e.count, st)
            v = self.ev(e.concat, st)
            if n is None:
                return self.conservative(e, st, w)
            return self.fit(v * n, w)
        if k == ExpressionKind.UnaryOp:
            return self.ev_unary(e, st, w)
        if k == ExpressionKind.BinaryOp:
            return self.ev_binary(e, st, w)
        if k == ExpressionKind.ConditionalOp:
            conds = list(e.conditions)
            if len(conds) == 1 and conds[0].pattern is None:
                ct = self.const_truth(conds[0].expr, st)
                if ct is not None:
                    self.stats["const_folds"] += 1
                    return self.fit(self.ev(e.left if ct else e.right, st), w)
            cm = 0
            for cnd in e.conditions:
                cm |= self.orall(self.ev(cnd.expr, st))
            a, b = self.fit(self.ev(e.left, st), w), self.fit(self.ev(e.right, st), w)
            return [x | y | cm for x, y in zip(a, b)]
        if k == ExpressionKind.Call:
            return self.ev_call(e, st, w)
        if k in (ExpressionKind.SimpleAssignmentPattern, ExpressionKind.StructuredAssignmentPattern,
                 ExpressionKind.ReplicatedAssignmentPattern):
            return self.ev_pattern(e, st, w)
        if k == ExpressionKind.Assignment:
            v = self.ev(e.right, st)
            self.assign(e.left, v, st)
            return self.fit(v, w)
        if k == ExpressionKind.Inside:
            m = self.orall(self.ev(e.left, st)) | self.all_reads(e, st)
            return [m] + [0] * (w - 1)
        return self.conservative(e, st, w)

    @staticmethod
    def fit(v, w):
        if len(v) >= w:
            return list(v[:w])
        return list(v) + [0] * (w - len(v))

    @staticmethod
    def orall(v):
        m = 0
        for x in v:
            m |= x
        return m

    def ev_select(self, e, st, w):
        base = self.ev(e.value, st)
        rng, ew = elem_info(e.value.type)
        if rng is None:
            return self.conservative(e, st, w)
        idx = self.cint(e.selector, st)
        if idx is not None:
            t = translate(rng, idx)
            if t is None:
                return [0] * w
            return self.fit(base[t * ew:(t + 1) * ew], w)
        sm = self.orall(self.ev(e.selector, st))
        n = len(base) // max(ew, 1)
        out = []
        for j in range(ew):
            m = sm
            for kk in range(n):
                if kk * ew + j < len(base):
                    m |= base[kk * ew + j]
            out.append(m)
        return self.fit(out, w)

    def ev_range(self, e, st, w):
        base = self.ev(e.value, st)
        rng, ew = elem_info(e.value.type)
        if rng is None:
            return self.conservative(e, st, w)
        sk = e.selectionKind
        if sk == RS.Simple:
            l, r = self.cint(e.left, st), self.cint(e.right, st)
            if l is None or r is None:
                return self.conservative(e, st, w)
            tl, tr = translate(rng, l), translate(rng, r)
            if tl is None or tr is None:
                return self.conservative(e, st, w)
            lo = min(tl, tr) * ew
            return self.fit(base[lo:lo + w], w)
        width = self.cint(e.right, st)
        b = self.cint(e.left, st)
        if b is not None and width is not None:
            first = b if sk == RS.IndexedUp else b - width + 1
            last = first + width - 1
            tl, tr = translate(rng, first), translate(rng, last)
            if tl is not None and tr is not None:
                lo = min(tl, tr) * ew
                return self.fit(base[lo:lo + w], w)
            return self.conservative(e, st, w)
        sm = self.orall(self.ev(e.left, st))
        out = []
        for j in range(w):
            m = sm
            for p in range(j, len(base)):
                m |= base[p]
            out.append(m)
        return out

    def ev_unary(self, e, st, w):
        op = e.op
        v = self.ev(e.operand, st)
        if op in (UO.BitwiseNot, UO.Plus):
            return self.fit(v, w)
        if op == UO.Minus:
            out, acc = [], 0
            for x in self.fit(v, w):
                acc |= x
                out.append(acc)
            return out
        if op in (UO.Preincrement, UO.Predecrement, UO.Postincrement, UO.Postdecrement):
            out, acc = [], 0
            for x in self.fit(v, w):
                acc |= x
                out.append(acc)
            self.assign(e.operand, out, st)
            return out
        m = self.orall(v)
        return [m] + [0] * (w - 1)

    def ev_binary(self, e, st, w):
        op = e.op
        if op in (BO.LogicalShiftLeft, BO.LogicalShiftRight, BO.ArithmeticShiftLeft, BO.ArithmeticShiftRight):
            a = self.fit(self.ev(e.left, st), w)
            n = self.cint(e.right, st)
            if n is not None:
                if op in (BO.LogicalShiftLeft, BO.ArithmeticShiftLeft):
                    return ([0] * min(n, w) + a)[:w]
                fill = a[-1] if (op == BO.ArithmeticShiftRight and getattr(e.left.type, "isSigned", False)) else 0
                return (a[n:] + [fill] * min(n, w))[:w]
            sm = self.orall(self.ev(e.right, st))
            out = []
            for j in range(w):
                m = sm
                rng = range(0, j + 1) if op in (BO.LogicalShiftLeft, BO.ArithmeticShiftLeft) else range(j, w)
                for p in rng:
                    m |= a[p]
                out.append(m)
            return out
        if op in (BO.BinaryAnd, BO.BinaryOr, BO.BinaryXor, BO.BinaryXnor):
            a, b = self.fit(self.ev(e.left, st), w), self.fit(self.ev(e.right, st), w)
            if op in (BO.BinaryAnd, BO.BinaryOr):
                kill = 0 if op == BO.BinaryAnd else 1
                ca, cb = self.const_bits(e.left, st, w), self.const_bits(e.right, st, w)
                if ca is not None or cb is not None:
                    self.stats["const_folds"] += 1
                    return [0 if ((ca is not None and ca[i] == kill) or (cb is not None and cb[i] == kill))
                            else (x | y) for i, (x, y) in enumerate(zip(a, b))]
            return [x | y for x, y in zip(a, b)]
        if op in (BO.LogicalAnd, BO.LogicalOr):
            kill = (op == BO.LogicalOr)
            for side in (e.left, e.right):
                if self.const_truth(side, st) is kill:
                    self.stats["const_folds"] += 1
                    return [0] * w
        if op in (BO.Add, BO.Subtract, BO.Multiply):
            a, b = self.fit(self.ev(e.left, st), w), self.fit(self.ev(e.right, st), w)
            out, acc = [], 0
            for x, y in zip(a, b):
                acc |= x | y
                out.append(acc)
            return out
        a, b = self.ev(e.left, st), self.ev(e.right, st)
        m = self.orall(a) | self.orall(b)
        if op in (BO.Divide, BO.Mod, BO.Power):
            return [m] * w
        return [m] + [0] * (w - 1)

    def ev_pattern(self, e, st, w):
        k = e.kind
        t = e.type
        fs = struct_fields(t)
        rng, ew = elem_info(t)
        out = [0] * w
        try:
            if k == ExpressionKind.SimpleAssignmentPattern:
                els = list(e.elements)
                if fs is not None:
                    for f, x in zip(fs, els):
                        off, fw = int(f.bitOffset), tw(f.type)
                        out[off:off + fw] = self.fit(self.ev(x, st), fw)
                    return self.fit(out, w)
                if rng is not None:
                    lo, hi = rng.left, rng.right
                    step = -1 if lo > hi else 1
                    for i, x in enumerate(els):
                        tpos = translate(rng, lo + i * step)
                        if tpos is None:
                            continue
                        out[tpos * ew:(tpos + 1) * ew] = self.fit(self.ev(x, st), ew)
                    return self.fit(out, w)
            if k == ExpressionKind.StructuredAssignmentPattern:
                dflt = e.defaultSetter
                if dflt is not None:
                    dv = self.ev(dflt, st)
                    dm = self.orall(dv)
                    if fs is not None or rng is not None:
                        unit = ew if (fs is None and rng is not None) else None
                        if unit:
                            pattern = self.fit(dv, unit)
                            out = (pattern * (w // unit + 1))[:w]
                        else:
                            out = [dm] * w
                    else:
                        out = self.fit(dv, w)
                for ms in e.memberSetters:
                    f = ms.member
                    off, fw = int(f.bitOffset), tw(f.type)
                    out[off:off + fw] = self.fit(self.ev(ms.expr, st), fw)
                for ix in e.indexSetters:
                    i = self.cint(ix.index, st)
                    if rng is None or i is None:
                        return self.conservative(e, st, w)
                    tpos = translate(rng, i)
                    if tpos is not None:
                        out[tpos * ew:(tpos + 1) * ew] = self.fit(self.ev(ix.expr, st), ew)
                if list(e.typeSetters):
                    return self.conservative(e, st, w)
                return self.fit(out, w)
        except Exception:  # noqa: BLE001
            return self.conservative(e, st, w)
        return self.conservative(e, st, w)

    def ev_call(self, e, st, w):
        args = list(e.arguments)
        if e.isSystemCall:
            name = e.subroutineName
            if name in ("$signed", "$unsigned") and args:
                return self.fit(self.ev(args[0], st), w)
            if name in ("$bits", "$clog2", "$size", "$high", "$low", "$left", "$right", "$increment",
                        "$dimensions", "$unpacked_dimensions", "$typename", "$isunbounded"):
                return [0] * w
            m = 0
            for a in args:
                if a.kind not in (ExpressionKind.DataType, ExpressionKind.EmptyArgument):
                    m |= self.orall(self.ev(a, st))
            return [m] * w
        sub = e.subroutine
        return self.call_user(sub, args, st, w)

    # ------------------------------------------------------------------ user subroutines
    def call_user(self, sub, args, st, w):
        fkey = self.key(sub)
        formals = list(sub.arguments)
        if fkey in self.fn_stack:
            m = 0
            for a in args:
                if a is not None and a.kind not in (ExpressionKind.EmptyArgument,):
                    m |= self.orall(self.ev(a, st))
            return [m] * w
        summ = self.fn_cache.get(fkey)
        if summ is None:
            self.fn_stack.append(fkey)
            try:
                summ = self.analyse_fn(sub, formals)
            finally:
                self.fn_stack.pop()
            self.fn_cache[fkey] = summ
        ph, phmask, ret, outs = summ
        actual = {}
        for f, a in zip(formals, args):
            if f.direction in (ArgumentDirection.In, ArgumentDirection.InOut, ArgumentDirection.Ref) and a is not None:
                first, fw = ph[f.name]
                av = self.fit(self.ev(a, st), fw)
                for i in range(fw):
                    actual[first + i] = av[i]

        def subst(m):
            r = m & ~phmask
            for b in iter_bits(m & phmask):
                r |= actual.get(b, 0)
            return r | st.ctrl | st.extra
        for f, a in zip(formals, args):
            if f.direction in (ArgumentDirection.Out, ArgumentDirection.InOut) and a is not None:
                lv = a.left if a.kind == ExpressionKind.Assignment else a
                self.assign(lv, [subst(x) for x in outs.get(f.name, [])], st)
        return self.fit([subst(x) for x in ret], w)

    def analyse_fn(self, sub, formals):
        st = State()
        ph, phmask = {}, 0
        for f in formals:
            fw = tw(f.type)
            first, _, _ = self.nodes_of("<ph>%s.%s" % (self.key(sub), f.name), fw, "<ph>", None)
            ph[f.name] = (first, fw)
            phmask |= ((1 << fw) - 1) << first
            if f.direction in (ArgumentDirection.In, ArgumentDirection.InOut, ArgumentDirection.Ref):
                st.env[self.key(f)] = tuple(1 << (first + i) for i in range(fw))
        rv = sub.returnValVar
        rw = tw(sub.returnType) if rv is not None else 0
        st.ret = [0] * rw
        self.exec(sub.body, st)
        ret = list(st.ret)
        if rv is not None:
            fin = st.env.get(self.key(rv))
            if fin is not None:
                ret = [r | (x or 0) for r, x in zip(ret, list(fin) + [0] * rw)]
        outs = {}
        for f in formals:
            if f.direction in (ArgumentDirection.Out, ArgumentDirection.InOut):
                v = st.env.get(self.key(f))
                outs[f.name] = [x or 0 for x in v] if v is not None else [0] * tw(f.type)
        return ph, phmask, ret, outs

    # ------------------------------------------------------------------ lvalues
    def lv_resolve(self, e, st):
        """-> list of (symbol, [offsets], width, dep mask)."""
        k = e.kind
        if k in (ExpressionKind.NamedValue, ExpressionKind.HierarchicalValue):
            return [(e.symbol, [0], tw(e.symbol.type), 0)]
        if k == ExpressionKind.Conversion:
            return self.lv_resolve(e.operand, st)
        if k in (ExpressionKind.ElementSelect, ExpressionKind.RangeSelect, ExpressionKind.MemberAccess):
            inner = self.lv_resolve(e.value, st)
            if len(inner) != 1:
                raise Unsupported("select of a concatenation lvalue")
            sym, offs, _, dep = inner[0]
            ww = tw(e.type)
            if k == ExpressionKind.MemberAccess:
                return [(sym, [o + int(e.member.bitOffset) for o in offs], ww, dep)]
            rng, ew = elem_info(e.value.type)
            if rng is None:
                raise Unsupported("select without a range")
            n = (max(rng.left, rng.right) - min(rng.left, rng.right) + 1)
            if k == ExpressionKind.ElementSelect:
                idx = self.cint(e.selector, st)
                if idx is not None:
                    t = translate(rng, idx)
                    return [(sym, [o + t * ew for o in offs] if t is not None else [], ww, dep)]
                dep |= self.orall(self.ev(e.selector, st))
                return [(sym, [o + kk * ew for o in offs for kk in range(n)], ww, dep)]
            sk = e.selectionKind
            if sk == RS.Simple:
                l, r = self.cint(e.left, st), self.cint(e.right, st)
                if l is None or r is None:
                    raise Unsupported("non-constant range select bounds")
                tl, tr = translate(rng, l), translate(rng, r)
                if tl is None or tr is None:
                    return [(sym, [], ww, dep)]          # out of range: the write changes nothing
                return [(sym, [o + min(tl, tr) * ew for o in offs], ww, dep)]
            width = self.cint(e.right, st)
            b = self.cint(e.left, st)
            if b is not None:
                first = b if sk == RS.IndexedUp else b - width + 1
                tl, tr = translate(rng, first), translate(rng, first + width - 1)
                if tl is None or tr is None:
                    return [(sym, [], ww, dep)]
                return [(sym, [o + min(tl, tr) * ew for o in offs], ww, dep)]
            dep |= self.orall(self.ev(e.left, st))
            return [(sym, [o + p * ew for o in offs for p in range(0, n - width + 1)], ww, dep)]
        if k == ExpressionKind.Concatenation:
            out = []
            for op in e.operands:
                out += self.lv_resolve(op, st)
            return out
        raise Unsupported("lvalue kind %s" % k)

    def assign(self, lhs, val, st):
        extra = st.ctrl | st.extra
        try:
            targets = self.lv_resolve(lhs, st)
        except Unsupported:
            self.fallbacks += 1
            m = self.orall(val) | extra
            syms = []

            def coll(n):
                if getattr(n, "kind", None) == ExpressionKind.NamedValue:
                    syms.append(n.symbol)
                return VisitAction.Advance
            lhs.visit(coll)
            for s in syms:
                if s.kind in (SymbolKind.Variable, SymbolKind.Net, SymbolKind.FormalArgument):
                    k = self.key(s)
                    cur = list(st.env.get(k) or [None] * tw(s.type))
                    own = self.own(s)
                    st.env[k] = tuple((own[i] if c is None else c) | m for i, c in enumerate(cur))
            return
        # concatenation lvalues take the value MSB-first
        pos = len(val)
        for sym, offs, ww, dep in targets:
            part = val[max(pos - ww, 0):pos] if len(targets) > 1 else self.fit(val, ww)
            pos -= ww
            part = self.fit(part, ww)
            if sym.kind not in (SymbolKind.Variable, SymbolKind.Net, SymbolKind.FormalArgument, SymbolKind.Port):
                continue
            k = self.key(sym)
            full = tw(sym.type)
            cur = list(st.env.get(k) or [None] * full)
            if len(cur) < full:
                cur += [None] * (full - len(cur))
            if len(offs) == 1 and dep == 0:
                o = offs[0]
                for j in range(ww):
                    if 0 <= o + j < full:
                        cur[o + j] = part[j] | extra
            else:
                own = self.own(sym)
                for o in offs:
                    for j in range(ww):
                        p = o + j
                        if 0 <= p < full:
                            old = own[p] if cur[p] is None else cur[p]
                            cur[p] = old | part[j] | dep | extra
            st.env[k] = tuple(cur)

    # ------------------------------------------------------------------ statements
    def merge(self, pre, branches):
        keys = set()
        for b in branches:
            for k, v in b.env.items():
                if pre.env.get(k) is not v:
                    keys.add(k)
        out = pre.fork()
        for k in keys:
            vals = [b.env.get(k) for b in branches]
            ref = next(v for v in vals if v is not None)
            n = len(ref)
            own_first = self.base.get(k)
            res = []
            for i in range(n):
                xs = [(v[i] if v is not None and i < len(v) else None) for v in vals]
                if all(x is None for x in xs):
                    res.append(None)
                    continue
                m = 0
                for x in xs:
                    if x is None:
                        m |= (1 << (own_first[0] + i)) if own_first else 0
                    else:
                        m |= x
                res.append(m)
            out.env[k] = tuple(res)
        rets = [b.ret for b in branches if b.ret is not None]
        if rets:
            out.ret = [self.orall(xs) for xs in zip(*rets)]
        for b in branches:
            out.extra |= b.extra
            out.brk |= b.brk
        return out

    def exec(self, s, st):
        k = s.kind
        if k in (StatementKind.List,):
            for x in s.list:
                self.exec(x, st)
            return
        if k == StatementKind.Block:
            self.exec(s.body, st)
            return
        if k == StatementKind.ExpressionStatement:
            e = s.expr
            if e.kind == ExpressionKind.Invalid:
                self.fallbacks += 1
                self.stats["fallback_kinds"]["Invalid"] = self.stats["fallback_kinds"].get("Invalid", 0) + 1
                return
            if e.kind == ExpressionKind.Assignment:
                v = self.ev(e.right, st)
                if e.isCompound:
                    v = self.compound(e, v, st)
                self.assign(e.left, self.fit(v, tw(e.left.type)), st)
            else:
                self.ev(e, st)
            return
        if k == StatementKind.VariableDeclaration:
            sym = s.symbol
            init = sym.initializer
            kk = self.key(sym)
            if init is not None:
                st.env[kk] = tuple(self.fit(self.ev(init, st), tw(sym.type)))
            else:
                st.env[kk] = tuple([0] * tw(sym.type))
            return
        if k == StatementKind.Conditional:
            conds = list(s.conditions)
            if len(conds) == 1 and conds[0].pattern is None:
                ct = self.const_truth(conds[0].expr, st)
                if ct is not None:
                    self.stats["const_folds"] += 1
                    if ct:
                        self.exec(s.ifTrue, st)
                    elif s.ifFalse is not None:
                        self.exec(s.ifFalse, st)
                    return
            cm = 0
            for cnd in conds:
                cm |= self.orall(self.ev(cnd.expr, st))
            t = st.fork()
            t.ctrl |= cm
            self.exec(s.ifTrue, t)
            f = st.fork()
            f.ctrl |= cm
            if s.ifFalse is not None:
                self.exec(s.ifFalse, f)
            t.ctrl = f.ctrl = st.ctrl
            merged = self.merge(st, [t, f])
            self.copy_into(st, merged)
            return
        if k == StatementKind.Case:
            subj = self.cint(s.expr, st) if self.fold else None
            if subj is not None and s.condition == CaseCond.Normal:
                hit = None
                allconst = True
                for it in s.items:
                    for x in it.expressions:
                        v = self.cint(x, st)
                        if v is None:
                            allconst = False
                        elif v == subj and hit is None:
                            hit = it
                if allconst:
                    self.stats["const_folds"] += 1
                    if hit is not None:
                        self.exec(hit.stmt, st)
                    elif s.defaultCase is not None:
                        self.exec(s.defaultCase, st)
                    return
            cm = self.orall(self.ev(s.expr, st))
            for it in s.items:
                for x in it.expressions:
                    cm |= self.all_reads(x, st)
            branches = []
            for it in s.items:
                b = st.fork()
                b.ctrl |= cm
                self.exec(it.stmt, b)
                b.ctrl = st.ctrl
                branches.append(b)
            if s.defaultCase is not None or not self.case_complete(s, st):
                b = st.fork()
                b.ctrl |= cm
                if s.defaultCase is not None:
                    self.exec(s.defaultCase, b)
                b.ctrl = st.ctrl
                branches.append(b)
            self.copy_into(st, self.merge(st, branches))
            return
        if k == StatementKind.ForLoop:
            self.exec_for(s, st)
            return
        if k in (StatementKind.ForeachLoop, StatementKind.WhileLoop, StatementKind.DoWhileLoop,
                 StatementKind.RepeatLoop, StatementKind.ForeverLoop):
            self.exec_fixpoint(s, st)
            return
        if k == StatementKind.Return:
            v = self.ev(s.expr, st) if s.expr is not None else []
            m = st.ctrl | st.extra
            if st.ret is not None and v:
                vv = self.fit(v, len(st.ret))
                st.ret = [r | x | m for r, x in zip(st.ret, vv)]
            st.extra |= st.ctrl
            return
        if k in (StatementKind.Break, StatementKind.Continue):
            st.extra |= st.ctrl
            st.brk |= 1
            return
        if k == StatementKind.Timed:
            self.exec(s.stmt, st)
            return
        if k in (StatementKind.Empty, StatementKind.ImmediateAssertion, StatementKind.ConcurrentAssertion,
                 StatementKind.Invalid, StatementKind.EventTrigger, StatementKind.Wait,
                 StatementKind.ProceduralChecker):
            return
        self.stats["unhandled_statements"][str(k).split(".")[-1]] = \
            self.stats["unhandled_statements"].get(str(k).split(".")[-1], 0) + 1

    def case_complete(self, s, st):
        """Whether the no-match path of a default-less case is dropped in this mode (see __init__)."""
        if self.mode == "lrm4":
            self.stats["case_no_default"] += 1
            return False
        if self.mode == "yosys" and str(s.check).split(".")[-1] in ("Unique", "Priority"):
            self.stats["case_full_by_qualifier"] += 1
            return True
        if s.condition != CaseCond.Normal:
            return False
        w = tw(s.expr.type)
        if w > 16:
            return False
        vals = set()
        for it in s.items:
            for x in it.expressions:
                v = self.cint(x, st)
                if v is None:
                    return False
                vals.add(v & ((1 << w) - 1))
        if len(vals) == (1 << w):
            self.stats["case_complete_2state"] += 1
            return True
        return False

    def compound(self, e, v, st):
        cur = self.ev(e.left, st)
        w = len(cur)
        v = self.fit(v, w)
        op = getattr(e, "op", None)
        if op in (BO.BinaryAnd, BO.BinaryOr, BO.BinaryXor):
            return [a | b for a, b in zip(cur, v)]
        out, acc = [], 0
        for a, b in zip(cur, v):
            acc |= a | b
            out.append(acc)
        if op in (BO.Divide, BO.Mod, BO.LogicalShiftRight, BO.ArithmeticShiftRight, BO.LogicalShiftLeft,
                  BO.ArithmeticShiftLeft):
            m = self.orall(cur) | self.orall(v)
            return [m] * w
        return out

    @staticmethod
    def copy_into(dst, src):
        dst.env, dst.ret, dst.extra, dst.brk = src.env, src.ret, src.extra, src.brk

    def exec_for(self, s, st):
        lvs = list(s.loopVars)
        for lv in lvs:
            self.loop_keys.add(self.key(lv))
        var = None
        if lvs:
            var = lvs[0]
            v0 = self.cint(var.initializer, st) if var.initializer is not None else None
        else:
            inits = list(s.initializers)
            v0 = None
            if len(inits) == 1 and inits[0].kind == ExpressionKind.Assignment and \
                    inits[0].left.kind == ExpressionKind.NamedValue:
                var = inits[0].left.symbol
                v0 = self.cint(inits[0].right, st)
        steps = list(s.steps)
        if var is not None and v0 is not None and len(lvs) <= 1 and len(steps) == 1 and s.stopExpr is not None:
            vk = self.key(var)
            val = v0
            exits = []
            for _ in range(MAX_UNROLL + 1):
                st.consts[vk] = val
                cond = self.cint(s.stopExpr, st)
                if cond is None:
                    break
                if not cond:
                    del st.consts[vk]
                    if exits:
                        self.copy_into(st, self.merge(st, exits + [st.fork()]))
                    return
                self.exec(s.body, st)
                if st.brk:
                    exits.append(st.fork())
                nxt = self.step_value(steps[0], vk, val, st)
                if nxt is None:
                    break
                val = nxt
            st.consts.pop(vk, None)
        self.exec_fixpoint(s, st)

    def step_value(self, step, vk, val, st):
        k = step.kind
        if k == ExpressionKind.UnaryOp:
            if step.op in (UO.Preincrement, UO.Postincrement):
                return val + 1
            if step.op in (UO.Predecrement, UO.Postdecrement):
                return val - 1
        if k == ExpressionKind.Assignment:
            st.consts[vk] = val
            if step.isCompound:
                r = self.cint(step.right, st)
                if r is None:
                    return None
                op = step.op
                return {BO.Add: val + r, BO.Subtract: val - r, BO.Multiply: val * r,
                        BO.LogicalShiftLeft: val << r, BO.LogicalShiftRight: val >> r}.get(op)
            return self.cint(step.right, st)
        return None

    def exec_fixpoint(self, s, st):
        """A loop whose trips are not unrolled: the body runs on the join of all earlier iterations until stable."""
        self.stats["fixpoint_loops"] += 1
        cm = 0
        for attr in ("stopExpr", "cond", "count"):
            x = getattr(s, attr, None)
            if x is not None and hasattr(x, "kind"):
                cm |= self.all_reads(x, st)
        loopvar_keys = []
        if s.kind == StatementKind.ForLoop:
            for lv in s.loopVars:
                loopvar_keys.append(self.key(lv))
        body = s.body
        cur = st.fork()
        for _ in range(64):
            b = cur.fork()
            b.ctrl |= cm
            for vk in loopvar_keys:
                b.consts.pop(vk, None)
            self.exec(body, b)
            b.ctrl = st.ctrl
            nxt = self.merge(cur, [cur, b])
            if all(nxt.env.get(k) == cur.env.get(k) for k in set(nxt.env) | set(cur.env)):
                break
            cur = nxt
        self.copy_into(st, cur)

    # ------------------------------------------------------------------ processes
    def commit(self, st, pid=None):
        for k, v in st.env.items():
            b = self.base.get(k)
            if b is None or k in self.loop_keys:
                continue
            first = b[0]
            for i, x in enumerate(v):
                if x is not None and i < b[1]:
                    self.edges[first + i] = self.edges.get(first + i, 0) | x
                    if pid is not None:
                        self.writer.setdefault(first + i, pid)

    def is_comb_block(self, pb):
        pk = pb.procedureKind
        if pk in (PK.AlwaysComb, PK.AlwaysLatch):
            return True
        if pk != PK.Always:
            return False
        b = pb.body
        if b.kind != StatementKind.Timed:
            return False
        tc = b.timing
        if tc.kind == TK.ImplicitEvent:
            return True
        evs = [tc] if tc.kind == TK.SignalEvent else (list(tc.events) if tc.kind == TK.EventList else None)
        if evs is None:
            return False
        return all(ev.kind == TK.SignalEvent and ev.edge == EdgeKind.None_ for ev in evs)

    def run(self):
        self.walk_scope(self.body)
        return self

    def walk_scope(self, scope):
        for m in scope:
            k = m.kind
            if k == SymbolKind.ContinuousAssign:
                st = State()
                a = m.assignment
                if a.kind != ExpressionKind.Assignment:
                    self.fallbacks += 1
                    self.stats["fallback_kinds"]["Invalid"] = self.stats["fallback_kinds"].get("Invalid", 0) + 1
                    continue
                self.assign(a.left, self.fit(self.ev(a.right, st), tw(a.left.type)), st)
                self.nproc += 1
                self.commit(st, self.nproc)
                self.stats["processes"]["assign"] += 1
            elif k == SymbolKind.ProceduralBlock:
                if self.is_comb_block(m):
                    st = State()
                    self.exec(m.body, st)
                    self.nproc += 1
                    self.commit(st, self.nproc)
                    self.stats["processes"]["comb"] += 1
                else:
                    self.stats["processes"]["other"] += 1
                    self.seq_block(m)
            elif k == SymbolKind.Net:
                self.sym_nodes(m)          # before the commit: a net initializer writes the net's own nodes
                if m.initializer is not None:
                    st = State()
                    st.env[self.key(m)] = tuple(self.fit(self.ev(m.initializer, st), tw(m.type)))
                    self.nproc += 1
                    self.commit(st, self.nproc)
                    self.stats["processes"]["net-init"] += 1
                self.sym_nodes(m)
            elif k == SymbolKind.Variable:
                self.sym_nodes(m)
            elif k == SymbolKind.Instance:
                self.instance(m)
            elif k == SymbolKind.InstanceArray:
                for el in m.elements:
                    if el.kind == SymbolKind.Instance:
                        self.instance(el)
            elif k == SymbolKind.GenerateBlock:
                if not m.isUninstantiated:
                    self.walk_scope(m)
            elif k == SymbolKind.GenerateBlockArray:
                for el in m.entries:
                    if not el.isUninstantiated:
                        self.walk_scope(el)
            elif k == SymbolKind.UninstantiatedDef:
                self.stats["uninstantiated"].append(m.definitionName)

    def seq_block(self, pb):
        """Hook for a non-combinational procedural block (edge processes, `initial`): nothing here (X9 overrides)."""
        return None

    def instance(self, inst):
        if not inst.isModule:
            self.stats["interfaces"] += 1
            return
        label = inst.hierarchicalPath
        top = self.body.hierarchicalPath
        if label.startswith(top + "."):
            label = label[len(top) + 1:]
        summ = {g: self.summaries(inst, g) for g in GRANULARITIES}
        ports = {}
        for p in inst.body:
            if p.kind == SymbolKind.Port:
                first, w, _ = self.nodes_of("<port>%s.%s" % (label, p.name), tw(p.type),
                                            "%s.%s" % (label, p.name), p.type)
                ports[p.name] = (first, w, p.direction)
                self.child_ports.append((label, p.name, str(p.direction).split(".")[-1]))
        for pc in inst.portConnections:
            p, e = pc.port, pc.expression
            if p is None or p.name not in ports or e is None:
                continue
            first, w, d = ports[p.name]
            st = State()
            if d == ArgumentDirection.In:
                v = self.fit(self.ev(e, st), w)
                self.commit(st)
                for i in range(w):
                    self.edges[first + i] = self.edges.get(first + i, 0) | v[i]
            elif d == ArgumentDirection.Out:
                lv = e.left if e.kind == ExpressionKind.Assignment else e
                self.assign(lv, [1 << (first + i) for i in range(w)], st)
                self.commit(st)
            else:
                self.stats["inout_ports"] += 1
        for g in GRANULARITIES:
            s = summ[g]
            # the child's input index is port-major and contiguous per port: translate masks block by block
            blocks, pos, prev = [], 0, None
            for pname, pbit in s["in_index"]:
                if pname != prev:
                    blocks.append([pname, pos, 0])
                    prev = pname
                blocks[-1][2] += 1
                pos += 1
            for out_name, bits in s["out"].items():
                if out_name not in ports:
                    continue
                first, w, _ = ports[out_name]
                for i, imask in enumerate(bits[:w]):
                    if not imask:
                        continue
                    m = 0
                    for pname, bpos, bw in blocks:
                        if pname in ports:
                            chunk = (imask >> bpos) & ((1 << bw) - 1)
                            if chunk:
                                m |= chunk << ports[pname][0]
                    if m:
                        self.child_edges[g][first + i] = self.child_edges[g].get(first + i, 0) | m


# ---------------------------------------------------------------------- graph algorithms

def sccs(n, edges_list):
    """Tarjan (iterative) over nodes 0..n-1 with adjacency given as lists of masks to OR. Returns nontrivial SCCs."""
    adj = {}
    for edges in edges_list:
        for u, m in edges.items():
            adj[u] = adj.get(u, 0) | m
    index, low, onstack, stack, out = {}, {}, set(), [], []
    counter = 0
    for root in list(adj.keys()):
        if root in index:
            continue
        work = [(root, iter(list(iter_bits(adj.get(root, 0)))))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        onstack.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for wv in it:
                if wv not in index:
                    index[wv] = low[wv] = counter
                    counter += 1
                    stack.append(wv)
                    onstack.add(wv)
                    work.append((wv, iter(list(iter_bits(adj.get(wv, 0))))))
                    advanced = True
                    break
                if wv in onstack:
                    low[v] = min(low[v], index[wv])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    x = stack.pop()
                    onstack.discard(x)
                    comp.append(x)
                    if x == v:
                        break
                if len(comp) > 1 or (adj.get(v, 0) >> v) & 1:
                    out.append(comp)
    return out, adj


def reach_inputs(adj, sources, sinks):
    """For every sink node, the mask (over source positions) of sources it depends on, cycles allowed."""
    pos = {s: i for i, s in enumerate(sources)}
    memo = {}
    # iterative DFS with SCC-insensitive fixpoint: compute by repeated relaxation over reverse topological order
    order, seen = [], set()
    for s in sinks:
        if s in seen:
            continue
        stack = [(s, iter(list(iter_bits(adj.get(s, 0)))))]
        seen.add(s)
        while stack:
            v, it = stack[-1]
            nxt = None
            for wv in it:
                if wv not in seen:
                    seen.add(wv)
                    nxt = wv
                    break
            if nxt is not None:
                stack.append((nxt, iter(list(iter_bits(adj.get(nxt, 0))))))
            else:
                stack.pop()
                order.append(v)
    for v in order:
        memo[v] = (1 << pos[v]) if v in pos else 0
    changed = True
    rounds = 0
    while changed and rounds < 1000:
        changed = False
        rounds += 1
        for v in order:
            m = memo[v]
            for wv in iter_bits(adj.get(v, 0)):
                m |= memo.get(wv, 0)
            if m != memo[v]:
                memo[v] = m
                changed = True
    return {s: memo.get(s, 0) for s in sinks}
