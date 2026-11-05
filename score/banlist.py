#!/usr/bin/env python3.12
"""svGolf operator banlist: per-task banned run-time operators.

A task bans the operator that IS the task (and whatever Yosys turns into the
same cell): the adder and multiplier tasks ban run-time `+ - * / % **` (Yosys's
`alumacc` merges `+` chains into the `$macc` cell that `*` becomes), the divider
bans `/ %`. Constant (elaboration-time) arithmetic stays allowed: parameter and
localparam expressions, genvar loops (`i = i + 1`), index arithmetic over
parameters and genvars (`a[i+1]`), procedural `for` loop counters (`k++`), and
constant functions evaluated at elaboration.

Two independent checks, both driven by the task's `banlist.operators`:

(a) FRONT CHECK (pyslang, `front_check`): elaborates the design with slang at
    the defaults and at each given parameter point, walks every RUN-TIME root
    (continuous assigns, procedural blocks, net and variable initializers,
    port connections, and the bodies of functions called from run-time code
    with a run-time argument, or whose body reads a signal from outside the
    function) and flags each banned operator node -- binary `+ - * / % **`,
    unary minus, `++`/`--`, compound assignments `+=` etc., and the array
    reduction methods `.sum()` (`+`) and `.product()` (`*`) -- whose operand
    subtree reads a run-time value. A subtree is CONSTANT when every name it
    reads is a parameter, localparam, genvar, enum value, or procedural `for`
    loop variable (loops are unrolled at elaboration), and every call in it is
    a system call or a user call with constant arguments whose body reads
    nothing from outside the function (its arguments, locals and return
    variable only, by declaration location). Reports `file:line:col`.

(b) BACKSTOP (Yosys, `backstop_check`): `proc; opt` at each given parameter
    point, BEFORE `alumacc` (so comparisons, `$lt` and friends, stay allowed),
    and rejects every cell of the banned operators' cell types (`$add $sub $neg
    $mul $div $mod $divfloor $modfloor $pow`, plus the post-`alumacc` and
    arithmetic-primitive types `$alu $macc $macc_v2 $lcu $fa`, which only appear
    this early when instantiated directly). Constant arithmetic is folded by
    Yosys before `proc` and leaves no cell. Reports the cell's `src` location.

A design passes the banlist iff both checks pass. The backstop is the ground
truth for what synthesis builds; the front check gives source locations and
also covers code that the scoring point does not elaborate (a generate branch
taken only at other parameter values).

Both checks read the source gate's canonical text (`srcgate.py`: no
preprocessor directives, attributes or synthesis pragmas; comments
stripped), so pyslang and Yosys read the same program.

Front-check details: a procedural loop counter is recognised by symbol
IDENTITY (its declaration), never by name, so a module signal `i` next to a
`for (int i ...)` is still a run-time value; a pre-declared variable used as
a counter (`for (k = 0; ...)`) is constant only inside that loop; a counter
that the loop body itself writes (`k = a[0];` inside the loop) is never
constant. The system
functions Yosys builds from `$add` chains (`$countones`, `$countbits`,
`$onehot`, `$onehot0`, `$isunknown`) are banned with `+` when their argument
is a run-time value.

Usage:
  python3.12 score/banlist.py SOLUTION.sv --top T --ban + - '*' [--point N=16 ...]
  python3.12 score/banlist.py SOLUTION.sv --task tasks/<name>
  python3.12 score/banlist.py --selftest
Prints JSON; exit status 0 = passes, 1 = banned operator found (or the design
does not elaborate), 2 = usage error.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

# the checker's sandbox package (environment scrub: no checker secret reaches a child process)
_CHECK_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "check")
if _CHECK_DIR not in sys.path:
    sys.path.insert(0, _CHECK_DIR)
import sandbox  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))

# operator -> Yosys cell types it becomes before `alumacc`
OP_CELLS = {
    "+": ["$add"],
    "-": ["$sub", "$neg"],
    "*": ["$mul"],
    "/": ["$div", "$divfloor"],
    "%": ["$mod", "$modfloor"],
    "**": ["$pow"],
}
# Arithmetic cells that only appear before `alumacc` when instantiated directly
# (`\$alu u(...)`); banned whenever any of + - * is.
ARITH_PRIMITIVES = ["$alu", "$macc", "$macc_v2", "$lcu", "$fa"]
ALL_OPS = list(OP_CELLS)


def banned_cells(ops):
    cells = set()
    for op in ops:
        cells.update(OP_CELLS[op])
    if set(ops) & {"+", "-", "*"}:
        cells.update(ARITH_PRIMITIVES)
    return sorted(cells)


# ---------------------------------------------------------------------------
# (a) front check: pyslang
# ---------------------------------------------------------------------------

def _slang():
    import pyslang  # noqa: F401  (python3.12, the extractor's interpreter)
    from pyslang import ast, syntax
    return ast, syntax


def _binop_symbol(ast, op):
    B = ast.BinaryOperator
    return {B.Add: "+", B.Subtract: "-", B.Multiply: "*", B.Divide: "/", B.Mod: "%",
            B.Power: "**"}.get(op)


def _unop_symbol(ast, op):
    U = ast.UnaryOperator
    return {U.Minus: "-", U.Preincrement: "+", U.Postincrement: "+",
            U.Predecrement: "-", U.Postdecrement: "-"}.get(op)


def _kind(node):
    return str(getattr(node, "kind", "")).split(".")[-1]


def _visit_all(root, ast):
    """Every AST node under `root` (expressions and statements), pre-order."""
    out = []

    def cb(node):
        out.append(node)
        return ast.VisitAction.Advance
    root.visit(cb)
    return out


CONST_SYMBOLS = {"Parameter", "EnumValue", "Specparam", "Genvar", "TypeParameter"}
# System functions that Yosys synthesizes from arithmetic cells (measured with
# Yosys 0.53 after `proc; opt`: each builds a `$add` chain), and the banned
# operator that makes them banned.
ARITH_SYSCALLS = {"$countones": "+", "$countbits": "+", "$onehot": "+", "$onehot0": "+",
                  "$isunknown": "+"}
# Array reduction methods that ARE arithmetic (IEEE 1800 §7.12.3); `.and()`,
# `.or()`, `.xor()` are bitwise and stay allowed. Yosys 0.53 cannot read any
# of them, but slang can, and a later Yosys may.
ARRAY_METHODS = {"sum": "+", "product": "*"}


class FrontCheck:
    def __init__(self, ops):
        self.ops = set(ops)
        self.findings = {}      # (file, line, col, op) -> message
        self.diagnostics = []
        self.reads_outside = {}   # subroutine key -> its body reads a non-local signal

    def run(self, sources, top, overrides):
        ast, syntax = _slang()
        options = ast.CompilationOptions()
        options.topModules = {top}
        if overrides:
            options.paramOverrides = [f"{k}={v}" for k, v in overrides.items()]
        import pyslang
        comp = ast.Compilation(pyslang.Bag([options]))
        trees = [syntax.SyntaxTree.fromFile(s) for s in sources]
        for t in trees:
            comp.addSyntaxTree(t)
        self.sm = trees[0].sourceManager if trees else None
        self.ast = ast
        for d in comp.getAllDiagnostics():
            if d.isError():
                self.diagnostics.append(f"slang error {d.code} at {self._loc_of_diag(d)}")
        # slang's ANALYSIS errors (multiple-always-assigns, mixed-var-assigns, "cannot assign
        # to input port", "'always' procedure does not advance time"): not in
        # getAllDiagnostics(); decided 2026-11-01 (slangdriver.py)
        import slangdriver
        self.diagnostics.extend(slangdriver.findings(trees, top, overrides))
        tops = [i for i in comp.getRoot().topInstances if i.name == top]
        if not tops:
            self.diagnostics.append(f"no top module {top!r}")
            return
        self.runtime_subs = {}
        roots = []
        self._collect_roots(tops[0].body, roots)
        done_subs = set()
        while roots:
            node = roots.pop()
            self._check_root(node, roots, done_subs)

    def _loc_of_diag(self, d):
        try:
            return f"{self.sm.getFileName(d.location)}:{self.sm.getLineNumber(d.location)}"
        except Exception:
            return "?"

    def _loc(self, node):
        loc = node.sourceRange.start
        return (os.path.realpath(str(self.sm.getFileName(loc))), self.sm.getLineNumber(loc),
                self.sm.getColumnNumber(loc))

    def _collect_roots(self, scope, roots):
        """Run-time roots in a scope (instance body / generate block), recursively."""
        ast = self.ast
        for m in scope:
            k = _kind(m)
            if k == "ContinuousAssign":
                roots.append(m.assignment)
            elif k == "ProceduralBlock":
                roots.append(m.body)
            elif k in ("Net", "Variable"):
                init = m.initializer
                if init is not None:
                    roots.append(init)
            elif k in ("GenerateBlock",):
                self._collect_roots(m, roots)
            elif k == "GenerateBlockArray":
                for entry in m.entries:
                    self._collect_roots(entry, roots)
            elif k == "Instance":
                for pc in m.portConnections:
                    e = pc.expression
                    if e is not None:
                        roots.append(e)
                self._collect_roots(m.body, roots)
            elif k == "InstanceArray":
                for e in m.elements:
                    if _kind(e) == "Instance":
                        for pc in e.portConnections:
                            if pc.expression is not None:
                                roots.append(pc.expression)
                        self._collect_roots(e.body, roots)

    @staticmethod
    def _sym_key(sym):
        """A symbol's identity: its declaration's source location (pybind11
        hands out a fresh wrapper object per access, so Python `id()` is not
        an identity; two symbols never share a declaration location)."""
        loc = sym.location
        return (sym.name, loc.buffer.id, loc.offset)

    @staticmethod
    def _range(node):
        r = node.sourceRange
        return (r.start.buffer.id, r.start.offset, r.end.offset)

    def _loop_vars(self, nodes):
        """Procedural `for` loop counters, by symbol IDENTITY (never by name: a
        module signal `i` next to a `for (int i ...)` stays a run-time
        value). A counter declared in the loop header is in scope only in the
        loop; a pre-declared variable used as the counter (`for (k = 0; ...)`)
        is treated as constant only inside that loop's source range."""
        lv = []
        for n in nodes:
            if _kind(n) == "ForLoop":
                written = self._written_keys(n.body)
                for v in (n.loopVars or []):
                    if self._sym_key(v) not in written:
                        lv.append((self._sym_key(v), None))
                rng = self._range(n)
                for init in (n.initializers or []):
                    if _kind(init) == "Assignment":
                        left = init.left
                        if _kind(left) == "NamedValue" and \
                                self._sym_key(left.symbol) not in written:
                            lv.append((self._sym_key(left.symbol), rng))
        return lv

    def _lvalue_roots(self, e):
        """The variables an assignment target writes: the root of each select
        or member access (`a[k] = ...` writes `a`, not `k`), every operand of
        a concatenation target."""
        k = _kind(e)
        if k == "NamedValue":
            return [e]
        if k in ("ElementSelect", "RangeSelect", "MemberAccess"):
            return self._lvalue_roots(e.value)
        if k == "Concatenation":
            return [r for o in e.operands for r in self._lvalue_roots(o)]
        if k == "Conversion":
            return self._lvalue_roots(e.operand)
        return []

    def _written_keys(self, body):
        """Symbols that a loop BODY writes (assignment, compound assignment,
        `++`/`--`). A loop counter the body writes is NOT unrolled into
        constants: Yosys silently ignores such a write (measured: `k =
        int'(a[0])` inside `for (int k ...)` synthesizes as if absent), so it
        is a run-time value for the banlist, and the extractor refuses the
        loop anyway."""
        keys = set()
        for m in _visit_all(body, self.ast):
            k = _kind(m)
            target = None
            if k == "Assignment":
                target = m.left
            elif k == "UnaryOp" and str(m.op).split(".")[-1] in (
                    "Preincrement", "Postincrement", "Predecrement", "Postdecrement"):
                target = m.operand
            if target is None:
                continue
            for r in self._lvalue_roots(target):
                keys.add(self._sym_key(r.symbol))
        return keys

    def _is_loop_var(self, n, loopvars):
        key = self._sym_key(n.symbol)
        start = n.sourceRange.start
        for k, rng in loopvars:
            if k != key:
                continue
            if rng is None or (start.buffer.id == rng[0] and rng[1] <= start.offset < rng[2]):
                return True
        return False

    def _is_const(self, node, loopvars):
        """Every name read under `node` is elaboration-time; every call is a system
        call or a user call whose arguments are themselves constant."""
        for n in _visit_all(node, self.ast):
            k = _kind(n)
            if k in ("NamedValue", "HierarchicalValue"):
                sk = str(n.symbol.kind).split(".")[-1]
                if sk in CONST_SYMBOLS:
                    continue
                if self._is_loop_var(n, loopvars):
                    continue
                return False
            if k == "Call" and not n.isSystemCall:
                if len(n.arguments) == 0:
                    return False   # a zero-argument user call may read module signals
                if self._reads_outside(n.subroutine):
                    return False   # constant arguments, but the body reads module signals
        return True

    def _reads_outside(self, sub):
        """Whether a user subroutine's body reads a non-constant name declared
        OUTSIDE the subroutine (a module signal, say), directly or through a
        call. Its arguments, locals and return variable are declared inside
        its syntax; parameters, genvars and enum values are constant. Such a
        function is run-time logic even when every argument is constant:
        `function automatic logic [15:0] g(input int k); g = a / b;
        endfunction  assign q = g(0);` divides `a` by `b` at run time."""
        if not hasattr(sub, "body"):
            return False
        key = self._sym_key(sub)
        if key in self.reads_outside:
            return self.reads_outside[key]
        self.reads_outside[key] = False      # a recursive call reads nothing new
        try:
            r = sub.syntax.sourceRange
            buf, lo, hi = r.start.buffer.id, r.start.offset, r.end.offset
        except Exception:
            self.reads_outside[key] = True   # no syntax to scope by: assume it does
            return True
        out = False
        for n in _visit_all(sub.body, self.ast):
            k = _kind(n)
            if k in ("NamedValue", "HierarchicalValue"):
                sym = n.symbol
                if str(sym.kind).split(".")[-1] in CONST_SYMBOLS:
                    continue
                loc = sym.location
                if loc.buffer.id == buf and lo <= loc.offset < hi:
                    continue
                out = True
                break
            if k == "Call" and not n.isSystemCall and self._reads_outside(n.subroutine):
                out = True
                break
        self.reads_outside[key] = out
        return out

    def _check_root(self, root, roots, done_subs):
        nodes = _visit_all(root, self.ast)
        loopvars = self._loop_vars(nodes)
        for n in nodes:
            k = _kind(n)
            op = None
            if k == "BinaryOp":
                op = _binop_symbol(self.ast, n.op)
                operands = [n.left, n.right]
            elif k == "UnaryOp":
                op = _unop_symbol(self.ast, n.op)
                operands = [n.operand]
            elif k == "Assignment" and n.isCompound:
                op = _binop_symbol(self.ast, n.op)
                operands = [n.left, n.right]
            elif k == "Call" and n.isSystemCall:
                name = n.subroutineName
                if name in ARRAY_METHODS:
                    op = ARRAY_METHODS[name]
                    what = (f"array reduction method `.{name}()` (run-time `{op}` over the "
                            "elements)")
                else:
                    op = ARITH_SYSCALLS.get(name)
                    what = f"`{name}` (Yosys builds it from `{op}` cells)"
                if op is None or op not in self.ops or self._is_const(n, loopvars):
                    continue
                f, line, col = self._loc(n)
                self.findings[(f, line, col, op)] = f"{f}:{line}:{col}: banned run-time {what}"
                continue
            elif k == "Call":
                if not self._is_const(n, loopvars):
                    sub = n.subroutine
                    key = self._sym_key(sub)
                    if key not in done_subs and hasattr(sub, "body"):
                        done_subs.add(key)
                        roots.append(sub.body)
                continue
            if op is None or op not in self.ops:
                continue
            if all(self._is_const(o, loopvars) for o in operands):
                continue
            f, line, col = self._loc(n)
            what = {"BinaryOp": f"binary `{op}`", "UnaryOp": "unary/inc-dec operator",
                    "Assignment": f"compound assignment `{op}=`"}[k]
            self.findings[(f, line, col, op)] = f"{f}:{line}:{col}: banned run-time {what}"


def front_check(sources, top, ops, points=()):
    """Findings (list of str) and diagnostics of the front check, at the
    defaults and at each parameter point (dict name -> value)."""
    fc = FrontCheck(ops)
    for overrides in [{}] + [dict(p) for p in points]:
        fc.run(sources, top, overrides)
    return sorted(fc.findings.values()), sorted(set(fc.diagnostics))


# ---------------------------------------------------------------------------
# (b) backstop: Yosys, after `proc; opt`, before `alumacc`
# ---------------------------------------------------------------------------

BACKSTOP_SCRIPT = """\
{reads}
hierarchy -check -top {top}{chparam}
proc
opt
write_json "{out}"
"""


def backstop_check(sources, top, ops, points=(), yosys=None):
    """Banned cells (list of str) after `proc; opt` at each point."""
    yosys = yosys or os.environ.get("SVGOLF_YOSYS") or "yosys"
    cells = set(banned_cells(ops))
    findings = []
    for point in (points or [{}]):
        workdir = tempfile.mkdtemp(prefix="svgolf-backstop-")
        try:
            out = os.path.join(workdir, "netlist.json")
            script = BACKSTOP_SCRIPT.format(
                reads="\n".join(f'read_verilog -sv "{os.path.abspath(s)}"' for s in sources),
                top=top, chparam="".join(f" -chparam {k} {v}" for k, v in dict(point).items()),
                out=out)
            with open(os.path.join(workdir, "b.ys"), "w") as fh:
                fh.write(script)
            exe = shutil.which(yosys) or yosys
            spec = sandbox.tool_spec([exe], read=[os.path.abspath(s) for s in sources] + [workdir],
                                     write=[workdir], label="yosys (banlist)")
            proc = sandbox.run([yosys, "-q", "-s", "b.ys"], spec,
                               env=sandbox.tool_env(workdir) if sandbox.policy().active else None,
                               cwd=workdir, timeout=1800, kind="tool", label="yosys (banlist)")
            if proc.returncode != 0:
                findings.append(f"yosys failed at {dict(point)}: "
                                f"{(proc.stderr or proc.stdout)[-1500:]}")
                continue
            with open(out) as fh:
                net = json.load(fh)
            for mname, mod in net.get("modules", {}).items():
                for cname, cell in mod.get("cells", {}).items():
                    if cell.get("type") in cells:
                        src = cell.get("attributes", {}).get("src", "?")
                        findings.append(f"{src}: banned cell {cell['type']} "
                                        f"(module {mname}, at {dict(point) or 'defaults'})")
        finally:
            shutil.rmtree(workdir, ignore_errors=True)
    return sorted(set(findings))


def check(sources, top, ops, points=(), yosys=None, gate=True):
    """Both checks. Returns a JSON-able dict with `passed`.

    With `gate` (the default), every source first goes through the source
    gate (`srcgate.py`) and both checks read its CANONICAL text, so that
    pyslang and Yosys read the same program (no `ifdef SYNTHESIS`, no
    `translate_off`). check.py passes `gate=False` because it hands over
    text that is already canonical."""
    if not ops:
        return {"passed": True, "banned_operators": [], "front": [], "backstop": [],
                "diagnostics": [], "source": []}
    workdir = tempfile.mkdtemp(prefix="svgolf-banlist-")
    try:
        if gate:
            import srcgate
            canon, findings = [], []
            for i, s in enumerate(sources):
                out = os.path.join(workdir, f"{i}_{os.path.basename(s)}")
                try:
                    srcgate.canonicalize(s, out, name=s)
                except srcgate.GateError as e:
                    findings += str(e).splitlines()
                canon.append(out)
            if findings:
                return {"passed": False, "banned_operators": list(ops), "source": findings,
                        "front": [], "backstop": [], "diagnostics": []}
            shown = dict(zip(canon, sources))
        else:
            canon, shown = list(sources), {}
        front, diags = front_check(canon, top, ops, points)
        back = backstop_check(canon, top, ops, points, yosys)

        def rename(xs):
            out = []
            for x in xs:
                for c, s in shown.items():
                    x = x.replace(os.path.realpath(c), s).replace(c, s)
                out.append(x)
            return out
        front, back, diags = rename(front), rename(back), rename(diags)
    finally:
        shutil.rmtree(workdir, ignore_errors=True)
    return {"passed": not front and not back and not diags,
            "banned_operators": list(ops), "banned_cells": banned_cells(ops),
            "points": [dict(p) for p in points], "source": [],
            "front": front, "backstop": back, "diagnostics": diags}


def task_banlist(task):
    b = task.get("banlist", {})
    ops = b.get("operators", [])
    for op in ops:
        if op not in OP_CELLS:
            raise SystemExit(f"task banlist: unknown operator {op!r} (known: {ALL_OPS})")
    pts = task.get("backstop_points") or [task["scoring"]["params"]]
    return ops, [{k: int(v) for k, v in p.items()} for p in pts]


# ---------------------------------------------------------------------------
# self test
# ---------------------------------------------------------------------------

def selftest():
    tests = os.path.join(HERE, "tests")
    arith = ["+", "-", "*", "/", "%", "**"]
    cases = [
        # file, top, expect_front_pass, expect_backstop_pass
        ("ok_constant.sv", "ok_constant", True, True),
        ("bad_add.sv", "bad_add", False, False),
        ("bad_compound.sv", "bad_compound", False, False),
        ("bad_neg.sv", "bad_neg", False, False),
        ("bad_mul.sv", "bad_mul", False, False),
        ("bad_incdec.sv", "bad_incdec", False, False),
        ("bad_index.sv", "bad_index", False, False),
        ("bad_loopname.sv", "bad_loopname", False, False),
        ("bad_countones.sv", "bad_countones", False, False),
        ("ok_countones_const.sv", "ok_countones_const", True, True),
        ("bad_predeclared_counter.sv", "bad_predeclared_counter", False, False),
        ("ok_predeclared_counter.sv", "ok_predeclared_counter", True, True),
        # A counter the loop body writes is run-time (front check); Yosys
        # ignores the write and folds the loop, so the backstop passes it.
        ("bad_counter_written.sv", "bad_counter_written", False, True),
    ]
    pts = [{"N": 16}]
    failures = 0
    for f, top, fp, bp in cases:
        src = [os.path.join(tests, f)]
        front, diags = front_check(src, top, arith, pts)
        back = backstop_check(src, top, arith, pts)
        ok = (not front and not diags) == fp and (not back) == bp
        failures += not ok
        print(f"[{'ok' if ok else 'FAIL'}] {f}: front {'pass' if not front else 'FLAG'}"
              f" {front[:2]}{' diags ' + str(diags) if diags else ''}; backstop"
              f" {'pass' if not back else 'FLAG'} {back[:2]}")
    # The divider banlist (/ %) on a constant function that divides: allowed.
    src = [os.path.join(tests, "ok_constfn.sv")]
    front, diags = front_check(src, "ok_constfn", ["/", "%"], pts)
    back = backstop_check(src, "ok_constfn", ["/", "%"], pts)
    ok = not front and not diags and not back
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] ok_constfn.sv (ban / %): front {front} {diags}; "
          f"backstop {back}")
    # A function called with a run-time argument is hardware: both checks flag it.
    src = [os.path.join(tests, "bad_runtime_fn.sv")]
    front, _ = front_check(src, "bad_runtime_fn", ["/", "%"], pts)
    back = backstop_check(src, "bad_runtime_fn", ["/", "%"], pts)
    ok = bool(front) and bool(back)
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] bad_runtime_fn.sv (ban / %): front {front}; backstop {back}")
    # A function called with CONSTANT arguments whose body reads module signals
    # is run-time logic: the front check scans its body. With a power-of-two
    # divisor (`a / 16`) the backstop sees no `$div` at all (Yosys folds it
    # into a shift before `proc; opt` ends), so only the front check catches
    # it; with `a / b` both do. A constant-argument function that reads only
    # its own arguments stays constant (ok_fn_const_args.sv).
    for f, top, want_back in (("bad_fn_const_args.sv", "bad_fn_const_args", True),
                              ("bad_fn_const_args_pow2.sv", "bad_fn_const_args_pow2", False),
                              ("bad_fn_const_in_expr.sv", "bad_fn_const_in_expr", False)):
        src = [os.path.join(tests, f)]
        front, _ = front_check(src, top, ["/", "%"], [{}])    # parameterless tops
        back = backstop_check(src, top, ["/", "%"], [{}])
        ok = bool(front) and bool(back) == want_back
        failures += not ok
        print(f"[{'ok' if ok else 'FAIL'}] {f} (ban / %): front {front[:1]}; backstop "
              f"{'FLAG' if back else 'pass'} (want {'FLAG' if want_back else 'pass'})")
    src = [os.path.join(tests, "ok_fn_const_args.sv")]
    front, diags = front_check(src, "ok_fn_const_args", ["/", "%"], [{}])
    back = backstop_check(src, "ok_fn_const_args", ["/", "%"], [{}])
    ok = not front and not diags and not back
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] ok_fn_const_args.sv (ban / %): front {front} {diags}; "
          f"backstop {back}")
    # Array reduction methods on run-time data: `.sum()` is `+`, `.product()`
    # is `*` (Yosys 0.53 cannot read them: the backstop fails, which also
    # rejects); `.xor()` is bitwise and the front check passes it.
    for f, top, want in (("bad_array_sum.sv", "bad_array_sum", True),
                         ("bad_array_product.sv", "bad_array_product", True),
                         ("ok_array_xor.sv", "ok_array_xor", False)):
        front, diags = front_check([os.path.join(tests, f)], top, arith, pts)
        ok = bool(front) == want and not diags
        failures += not ok
        print(f"[{'ok' if ok else 'FAIL'}] {f}: front {'FLAG' if front else 'pass'} {front[:1]} "
              f"{diags} (want {'FLAG' if want else 'pass'})")
    # A banned operator in a generate branch the scoring point does not take:
    # the backstop cannot see it (no cell is built at N=16), the front check does.
    src = [os.path.join(tests, "bad_hidden_branch.sv")]
    front, _ = front_check(src, "bad_hidden_branch", arith, pts)
    back = backstop_check(src, "bad_hidden_branch", arith, pts)
    ok = bool(front) and not back
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] bad_hidden_branch.sv: front {front}; backstop {back} "
          "(expected: front flags, backstop passes)")
    # The backstop ALONE catches each run-time operator (the front check is
    # bypassed: the checks are independent).
    for f, top in (("bad_add.sv", "bad_add"), ("bad_compound.sv", "bad_compound"),
                   ("bad_neg.sv", "bad_neg"), ("bad_mul.sv", "bad_mul"),
                   ("bad_incdec.sv", "bad_incdec"), ("bad_loopname.sv", "bad_loopname"),
                   ("bad_countones.sv", "bad_countones")):
        back = backstop_check([os.path.join(tests, f)], top, arith, pts)
        ok = bool(back)
        failures += not ok
        print(f"[{'ok' if ok else 'FAIL'}] backstop alone flags {f}: {back[:1]}")
    # `check()` gates the source first: an `ifdef SYNTHESIS` design is
    # rejected before either check runs (pyslang and Yosys would read
    # different programs).
    res = check([os.path.join(tests, "gate", "ifdef_synth.sv")], "band", arith, pts)
    ok = not res["passed"] and bool(res["source"])
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] check() rejects gate/ifdef_synth.sv at the source "
          f"gate: {res['source'][:1]}")
    # slang's ANALYSIS errors are front-check diagnostics, at every point (decided 2026-11-01;
    # slangdriver.py): the fixtures are fourstate's, none has an arithmetic operator
    for f, want, point in (("analysis_two_always", "MultipleAlwaysAssigns", {"N": 16}),
                           ("analysis_mixed", "MixedVarAssigns", {"N": 16}),
                           ("analysis_input", "InputPortAssign", {"N": 16}),
                           ("analysis_initial_comb", "MultipleAlwaysAssigns", {"N": 16}),
                           ("analysis_always_notime", "AlwaysWithoutTimingControl", {"N": 16}),
                           ("analysis_point", "MultipleAlwaysAssigns", {"N": 2})):
        src = [os.path.join(tests, "fourstate", f + ".sv")]
        front, diags = front_check(src, f, arith, [point])
        ok = not front and any(f"slang analysis error {want} at" in dg for dg in diags)
        failures += not ok
        print(f"[{'ok' if ok else 'FAIL'}] {f}.sv: front diagnostics {[dg.split(':')[0][:60] for dg in diags][:2]}"
              f" (want slang analysis error {want})")
    # the verdict is per point: the same design is clean at N = 4 (the default is N = 4 too)
    front, diags = front_check([os.path.join(tests, "fourstate", "analysis_point.sv")],
                               "analysis_point", arith, [{"N": 4}])
    ok = not front and not diags
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] analysis_point.sv at N = 4: front {front} {diags}")
    # An empty banlist passes everything.
    ok = check([os.path.join(tests, "bad_add.sv")], "bad_add", [])["passed"]
    failures += not ok
    print(f"[{'ok' if ok else 'FAIL'}] empty banlist passes bad_add.sv")
    print("selftest:", "PASS" if not failures else f"{failures} FAILED")
    return 1 if failures else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="*")
    ap.add_argument("--top")
    ap.add_argument("--ban", nargs="+", default=None)
    ap.add_argument("--point", action="append", help="NAME=VALUE[,NAME=VALUE]")
    ap.add_argument("--task")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if not args.sources:
        ap.error("no source files")
    if args.task:
        with open(os.path.join(args.task, "task.json")) as fh:
            task = json.load(fh)
        ops, pts = task_banlist(task)
        top = task["top"]
    else:
        if not args.top or args.ban is None:
            ap.error("--top and --ban (or --task) are required")
        top, ops = args.top, args.ban
        pts = []
        for p in args.point or []:
            pts.append({kv.split("=")[0]: int(kv.split("=")[1]) for kv in p.split(",")})
    res = check(args.sources, top, ops, pts)
    print(json.dumps(res, indent=2, sort_keys=True))
    return 0 if res["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
