#!/usr/bin/env python3.12
"""svGolf 4-state rules: no x or z value can arise at the parameter points the checker probes.

ls-sv, like IEEE 1800 simulation, computes with 4-state values: an unknown
bit is `x`, and the language decides what an `x` does at each construct --
`if (x)` takes the else branch, a case item matches only by `===` (an `x`
selector or item never matches a known value), `x ? a : b` merges the arms.
Yosys reads an `x` (and a `z`) as a synthesis DON'T-CARE: it drops x/z bits
from comparisons, resolves an unknown mux select to whichever arm it likes,
and treats an undriven net (`opt -full`'s `-undriven`) and an out-of-range
read (`$shiftx`) as undefined. Wherever an `x` reaches a decision, the
circuit ls-sv proves and the circuit Yosys scores can therefore differ, and
the player chooses where (measured with Yosys 0.53, `tests/_example/attacks/`):
`logic u; assign t = u ? 1'b0 : 1'b1; if (t) y = a | b; else y = a & b;` is
`a & b` to ls-sv and IEEE (t is x, the if takes the else branch) and
`a | b` to Yosys; `t = k[i + 4] ? ...` with `i + 4` always beyond `k`'s
range, the same. The post-synthesis check would find these only where its
vectors hit the difference, and a player can confine it to a rare region.

So svGolf refuses every SOURCE of an x or z value, exactly, instead of
sampling for its consequences. The literal sources (`1'bz`, `'x`, `4'b1?00`
outside a casez/casex item wildcard) are the source gate's (`srcgate.py`,
lexical, parameter-independent). This module refuses the rest, at one
parameter point (`check`) or at a list of them (`check_points`). The checker
stage `fourstate` runs it at EVERY point it probes, the scoring point first
(the design that is scored), then the task's probe and backstop points
(since 2026-11-06; before, at the scoring point only, while the statement
covers every parameter value in range: the universal-correctness audit's
`band_undrv.sv` is undriven only away from N = 16, and the pinned flow's
N = 8 netlist computes `a | b` where ls-sv computes `a & b`). That NARROWS
the gap, it does not close it: a point nobody probes is still unchecked, and
the statement resolves an x the simulator's way (`if (x)` takes the else
branch) until ls-sv's every-resolution semantics lands. The rules:

  (a) PARAMETERS (slang): every parameter and localparam of every instance
      whose elaborated value has an unknown bit (`localparam logic [3:0] K =
      4'd1 / 4'd0;`, `{P[5], 1'b0}` with `P` four bits wide);
  (b) CONSTANT EXPRESSIONS (slang): every expression in run-time code (the
      banlist's run-time roots: continuous assigns, procedural blocks,
      initializers, port connections, and the bodies of the functions they
      call) that slang evaluates as a constant with an unknown bit (an
      inline `4'd3 / 4'd0`, `0 ** -1`, an out-of-range part select of a
      parameter, a constant function returning an unassigned local);
  (c) slang's own diagnostics for an x-producing constant: `DivisionByZero`,
      `IndexOOB`, `RangeOOB`, `RangeWidthOOB` (a constant index or range
      outside the declared range, read or write), `GenvarUnknownBits`,
      `EnumValueUnknownBits`, `CaseZWithX`;
  (d) RUN-TIME SELECTS (slang): every bit/element select `v[i]` and indexed
      part select `v[i +: W]` / `v[i -: W]` whose index is not a constant
      (`$bits(v) - 1` and the other type and array queries of a signal are
      constants, IEEE 1800-2023 §20.6.2, §20.7) and can, by its type alone (an unsigned w-bit index ranges over
      0 .. 2^w - 1, a signed one over negative values too), address outside
      `v`'s declared range. An out-of-range read is x. Declare the range to
      cover every index value (pad an array to a power of two) or narrow the
      index. One exception, a WRITE: a bit/element select of a packed
      vector that an assignment writes through, with an UNSIGNED index that
      can only pass the top of the range, is admitted, because an out-of-range write has
      no effect (IEEE 1800-2023 §11.5.1), in ls-sv (`resolveLhs2`) and in
      Yosys (measured, txtask-v2 review fixture 14); a signed write index
      stays refused (ls-sv reads every index unsigned, the standard a
      signed one as a negative number), and so does an indexed part select
      written partly out of range. A procedural loop counter is a run-time
      index here (it is an `int`): ls-sv does not load procedural loops
      today, and a PR that admits them should teach this rule loop bounds;
  (e) UNDRIVEN AND CONFLICTING NETS (Yosys): `proc; flatten; check -assert`
      at each point checked, like rules (a) to (d) (in the checker: the
      scoring point, then the probe and backstop points; before 2026-11-06
      the scoring point alone) -- a wire bit that is used but has no driver
      (it reads as x), two or more conflicting drivers, or a combinational
      logic loop; `proc`'s own refusal of an always_comb block that
      reads a variable it does not assign on every path (a latch: x until
      assigned); and, since WP-PROC follow-up 3 (2026-11-01), any latch
      `proc` infers (`select -assert-none t:$dlatch t:$adlatch t:$dlatchsr`),
      which is how an `always @*` block or an `always_latch` that assigns a
      variable on some paths only is refused at the original text, whatever
      ls-sv accepts (defense in depth for the always @* lowering's rule R5,
      docs/sv-proc-lowering.md). The clocked tasks DEPEND on the undriven
      check (txtask-v2, decided 2026-11-06): rule 2 reads a variable no
      process writes as a constant power-up value and Yosys as undefined,
      and a register bit no write reaches gets no flop at all, so check.py's
      never-loaded rule (the flow's log) never sees it; this check is the
      one that refuses both (tests/seq_counter/never_loaded/partial.sv).

What it does not cover: an x that a Yosys or ls-sv BUG introduces (that is
the post-synthesis check's job, `check/postsynth.py`); run-time division or
remainder by zero, and `**` with a negative exponent (an x in IEEE from known
operands): no rule here, because every task bans run-time `/ % **` since
2026-11-06 (`banlist.py` `ALWAYS_BANNED`, added to every task's list; until
then `clmul`, `aes_sbox`, `matmul` and `sorter` admitted them, and this
docstring wrongly said every task banned `/` and `%`), and in the clocked
tasks txtask-v2's rule 3 (`XSafe`, `SvGolf/TaskSeq.lean`) also refuses, in
the proof, a divisor that is not a nonzero constant; a function-local variable or return value read before it is assigned
(x in IEEE, resolved freely by Yosys, which inlines the function; measured
in `tests/_example/attacks/fn_uninit.sv`): ls-sv has no user function calls
yet, so such a design cannot be proved (the post-synthesis check fails
closed on it), and an ls-sv PR that adds calls needs a rule here first; a
latch that is never loaded (`always_latch`, or an `always @*` block that
assigns a variable only on some paths): x in IEEE, resolved to 0 by Yosys
(measured in `tests/_example/attacks/latch_never.sv` and `latch_star.sv`):
every latch `proc` infers is refused by rule (e) now (a latch of a design
ls-sv could model would need its own initial-x rule first). An unassigned
variable of an `always_comb` block is Yosys's own refusal (`proc`: "Latch
inferred ... from always_comb process"), which rule (e) also reports.

Usage:
  python3.12 score/fourstate.py DESIGN.sv --top T [--point N=16]
  python3.12 score/fourstate.py DESIGN.sv --task tasks/<name>  # its scoring point
  python3.12 score/fourstate.py --selftest
Prints JSON {passed, findings, seconds}; exit status 0 = passes, 1 = refused
(or the design does not elaborate), 2 = usage or infrastructure error. The
source is read as is: check.py hands over the source gate's canonical text;
standalone, the file is gated first.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

# the checker's sandbox package (environment scrub: no checker secret reaches a child process)
_CHECK_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "check")
if _CHECK_DIR not in sys.path:
    sys.path.insert(0, _CHECK_DIR)
import sandbox  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import banlist  # noqa: E402  (its run-time root walker, `FrontCheck`)

# The type and array query functions, constant for a fixed-size argument (rule (d)'s constant index).
QUERY_CALLS = {"$bits", "$size", "$high", "$low", "$left", "$right", "$increment", "$dimensions",
               "$unpacked_dimensions"}
# slang diagnostics that mean "this constant is x" (rule c).
X_DIAGS = {"DivisionByZero", "IndexOOB", "RangeOOB", "RangeWidthOOB", "GenvarUnknownBits",
           "EnumValueUnknownBits", "CaseZWithX"}
# Expression kinds an x can be born at in a constant evaluation (rule b);
# the others only propagate one.
EVAL_KINDS = {"BinaryOp", "UnaryOp", "ElementSelect", "RangeSelect", "Call", "NamedValue"}

YOSYS_CHECK = """\
{reads}
hierarchy -check -top {top}{chparam}
proc
tee -q -o latches.txt dump t:$dlatch t:$adlatch t:$dlatchsr
select -assert-none t:$dlatch t:$adlatch t:$dlatchsr
flatten
check -assert
"""


class InfraError(Exception):
    pass


class XCheck(banlist.FrontCheck):
    """The slang rules (a) to (d), on the banlist's run-time roots."""

    def __init__(self):
        super().__init__([])
        self.xfind = {}     # (file, line, col) -> message

    def add(self, node_or_loc, msg):
        f, line, col = node_or_loc if isinstance(node_or_loc, tuple) else self._loc(node_or_loc)
        self.xfind.setdefault((f, line, col), f"{f}:{line}:{col}: {msg}")

    def run(self, sources, top, overrides):
        ast, syntax = banlist._slang()
        import pyslang
        options = ast.CompilationOptions()
        options.topModules = {top}
        if overrides:
            options.paramOverrides = [f"{k}={v}" for k, v in overrides.items()]
        comp = ast.Compilation(pyslang.Bag([options]))
        # From TEXT, never `fromFile`: pyslang caches files by path for the
        # whole process, so a second design written to a reused path would be
        # read as the first (measured).
        trees, sm = [], pyslang.SourceManager()
        for s in sources:
            with open(s) as fh:
                trees.append(syntax.SyntaxTree.fromText(fh.read(), sm, os.path.realpath(s)))
        for t in trees:
            comp.addSyntaxTree(t)
        self.sm = trees[0].sourceManager if trees else None
        self.ast = ast
        for d in comp.getAllDiagnostics():
            code = str(d.code).split("(")[-1].rstrip(")")
            if d.isError():
                self.diagnostics.append(f"slang error {code} at {self._loc_of_diag(d)}")
            elif code in X_DIAGS:
                loc = d.location
                self.add((os.path.realpath(str(self.sm.getFileName(loc))),
                          self.sm.getLineNumber(loc), self.sm.getColumnNumber(loc)),
                         f"slang {code}: this constant is x (an out-of-range index or range, "
                         "a division by zero, unknown bits); ls-sv and Yosys give x different "
                         "meanings")
        # slang's ANALYSIS errors (multiple-always-assigns, mixed-var-assigns, "cannot assign
        # to input port", "'always' procedure does not advance time"): not in
        # getAllDiagnostics(); decided 2026-11-01 (slangdriver.py)
        import slangdriver
        self.diagnostics.extend(slangdriver.findings(trees, top, overrides))
        tops = [i for i in comp.getRoot().topInstances if i.name == top]
        if not tops:
            self.diagnostics.append(f"no top module {top!r}")
            return
        self.scope = tops[0].body

        # (a) parameters of every instance, generate blocks included
        def params(node):
            if banlist._kind(node) == "Parameter":
                v = node.value
                if v is not None and v.hasUnknown():
                    loc = node.location
                    self.add((os.path.realpath(str(self.sm.getFileName(loc))),
                              self.sm.getLineNumber(loc), self.sm.getColumnNumber(loc)),
                             f"parameter `{node.name}` = {v} has unknown bits (ls-sv computes "
                             "with them, Yosys reads them as don't-cares)")
            return ast.VisitAction.Advance
        tops[0].body.visit(params)

        roots = []
        self._collect_roots(tops[0].body, roots)
        done_subs = set()
        while roots:
            self._check_root(roots.pop(), roots, done_subs)

    def _const_value(self, n):
        try:
            v = n.eval(self.ast.EvalContext(self.scope))
        except Exception:      # noqa: BLE001  (not a constant here)
            return None
        return v if v else None

    def _is_index_const(self, e):
        """Rule (d)'s constant index: one that reads no run-time name (`banlist._is_const`), or one slang evaluates to
        a known constant whose every run-time name is the argument of a type or array query function (IEEE
        1800-2023 §20.6.2, §20.7: `$bits` and the array queries of a fixed-size argument are constant, so
        `sq[$bits(sq) - 1]` is a constant select: the 2026-11-06 adversarial round's finding F3, MEASURED, which
        this rule refused as a run-time signed index)."""
        if self._is_const(e, []):
            return True
        v = self._const_value(e)
        if v is None or v.hasUnknown():
            return False
        spans = []
        for n in banlist._visit_all(e, self.ast):
            k = banlist._kind(n)
            if k == "Call" and n.isSystemCall and n.subroutineName in QUERY_CALLS:
                spans.append((n.sourceRange.start.offset, n.sourceRange.end.offset))
            elif k in ("NamedValue", "HierarchicalValue"):
                if str(n.symbol.kind).split(".")[-1] in banlist.CONST_SYMBOLS:
                    continue
                at = n.sourceRange.start.offset
                if not any(lo <= at < hi for lo, hi in spans):
                    return False
        return True

    def _check_root(self, root, roots, done_subs):
        ast = self.ast
        nodes = banlist._visit_all(root, ast)
        writes = set()
        for n in nodes:
            if banlist._kind(n) == "Assignment":
                self._mark_writes(n.left, writes)
        for n in nodes:
            k = banlist._kind(n)
            if k == "Call" and not n.isSystemCall and not self._is_const(n, []):
                sub = n.subroutine
                key = self._sym_key(sub)
                if key not in done_subs and hasattr(sub, "body"):
                    done_subs.add(key)
                    roots.append(sub.body)
            # (b) constant expressions that evaluate to x
            if k in EVAL_KINDS:
                v = self._const_value(n)
                if v is not None and v.hasUnknown():
                    self.add(n, f"`{self._text(n)}` is the constant {v}, which has unknown bits "
                             "(ls-sv computes with them, Yosys reads them as don't-cares)")
                    continue
            # (d) run-time selects that can leave the declared range
            if k == "ElementSelect":
                self._check_select(n, n.selector, 1, "up", write=self._key(n) in writes)
            elif k == "RangeSelect":
                sk = str(n.selectionKind).split(".")[-1]
                if sk in ("IndexedUp", "IndexedDown"):
                    w = self._const_value(n.right)
                    width = int(w.value) if w is not None and not w.hasUnknown() else None
                    self._check_select(n, n.left, width, "up" if sk == "IndexedUp" else "down")

    def _key(self, n):
        return (self._loc(n), n.sourceRange.end.offset)

    def _mark_writes(self, lhs, writes):
        """The element selects an assignment target writes through: the target itself and every
        select on its path (`m[i][j]`, a concatenation's parts), never a select inside an index."""
        k = banlist._kind(lhs)
        if k == "ElementSelect":
            writes.add(self._key(lhs))
            self._mark_writes(lhs.value, writes)
        elif k == "Concatenation":
            for o in lhs.operands:
                self._mark_writes(o, writes)
        elif k in ("RangeSelect", "MemberAccess"):
            self._mark_writes(lhs.value, writes)

    def _text(self, n):
        s = n.syntax
        return " ".join(str(s).split())[:60] if s is not None else banlist._kind(n)

    def _check_select(self, n, index, width, direction, write=False):
        if self._is_index_const(index):
            return                    # rule (c): slang's IndexOOB / RangeOOB
        try:
            t = n.value.type
            rng = t.fixedRange
            lo, hi = rng.lower, rng.upper
        except Exception:      # noqa: BLE001
            self.add(n, f"run-time select `{self._text(n)}` on a value without a fixed range "
                     "(cannot show that it stays in range)")
            return
        it = index.type
        w, signed = it.bitWidth, it.isSigned
        imin, imax = ((-(1 << (w - 1)), (1 << (w - 1)) - 1) if signed else (0, (1 << w) - 1))
        if width is None:
            self.add(n, f"indexed part select `{self._text(n)}` with a non-constant width")
            return
        if direction == "up":
            amin, amax = imin, imax + width - 1
        else:
            amin, amax = imin - width + 1, imax
        if lo <= amin and amax <= hi:
            return
        if write and not signed and lo <= amin and t.isIntegral:
            return        # an out-of-range write into a vector has no effect (rule (d)'s exception)
        why = ("a signed write index can be negative, which the standard reads as out of range (no "
               "effect) and ls-sv as an unsigned number" if write else
               "an out-of-range read is x, which ls-sv and Yosys give different meanings")
        self.add(n, f"run-time index in `{self._text(n)}`: a {'signed ' if signed else ''}"
                 f"{w}-bit index addresses {amin}..{amax}, outside the declared range "
                 f"[{hi}:{lo}] ({why}); cover every index value in the declaration or narrow the index"
                 + ("; if this is a procedural `for` counter (an `int`), the loop itself is the problem: "
                    "this rule does not know loop bounds yet, so write it as a generate-for with a genvar"
                    if signed and w == 32 else ""))


def slang_check(sources, top, point):
    xc = XCheck()
    xc.run(sources, top, dict(point))
    return sorted(xc.xfind.values()), sorted(set(xc.diagnostics))


def latch_finding(work, at):
    """Rule (e), latches: the message for the `select -assert-none t:$dlatch ...` that failed after `proc`; the latched
    signals come from the `dump` Yosys wrote (`connect \\Q <signal>` of each latch cell)."""
    sigs = []
    try:
        with open(os.path.join(work, "latches.txt")) as fh:
            for ln in fh:
                m = re.match(r"\s*connect \\Q (\S+)", ln)
                if m and m.group(1) not in sigs:
                    sigs.append(m.group(1).lstrip("\\"))
    except OSError:
        pass
    named = " for " + ", ".join(f"`{x}`" for x in sorted(sigs)) if sigs else ""
    return (f"Yosys at {at}: `proc` inferred a latch{named}: an `always @*` or `always_latch` block that assigns a "
            "variable on some paths only keeps its old value, which is x in IEEE simulation until the first "
            "assignment (ls-sv computes with the x), where Yosys resolves a never-loaded latch freely "
            "(tests/_example/attacks/latch_never.sv and latch_star.sv); assign it on every path")


def yosys_check(sources, top, point, yosys=None):
    """Rule (e): `check -assert` after `proc; flatten` at the point."""
    yosys = yosys or os.environ.get("SVGOLF_YOSYS") or shutil.which("yosys")
    if not yosys:
        raise InfraError("yosys not found")
    work = tempfile.mkdtemp(prefix="svgolf-fourstate-")
    try:
        script = YOSYS_CHECK.format(
            reads="\n".join(f'read_verilog -sv "{os.path.abspath(s)}"' for s in sources),
            top=top, chparam="".join(f" -chparam {k} {v}" for k, v in dict(point).items()))
        with open(os.path.join(work, "c.ys"), "w") as fh:
            fh.write(script)
        exe = shutil.which(yosys) or yosys
        spec = sandbox.tool_spec([exe], read=[os.path.abspath(s) for s in sources] + [work], write=[work],
                                 label="yosys (fourstate)")
        p = sandbox.run([yosys, "-q", "-s", "c.ys"], spec,
                        env=sandbox.tool_env(work) if sandbox.policy().active else None,
                        cwd=work, timeout=1800, kind="tool", label="yosys (fourstate)")
        if p.returncode == 0:
            return []
        out = p.stderr + p.stdout
        at = dict(point) or "defaults"
        if "problems in 'check -assert'" in out:
            warn = [ln.strip()[len("Warning: "):] for ln in out.splitlines()
                    if ln.startswith("Warning:") and "tri-state" not in ln]
            return [f"Yosys `check` at {at}: {w}" + (
                " (an undriven bit reads as x: ls-sv computes with it, Yosys resolves it "
                "freely)" if "no driver" in w else "") for w in warn] or \
                [f"Yosys `check -assert` failed at {at}: {out.strip()[-600:]}"]
        if "selection is not empty" in out and "dlatch" in out:
            return [latch_finding(work, at)]
        err = [ln.strip() for ln in out.splitlines() if ln.startswith("ERROR")]
        if any("Latch inferred" in e for e in err):
            return [f"Yosys at {at}: {err[0][len('ERROR: '):]} (a variable an always_comb "
                    "block reads before it assigns it on every path holds x)"]
        return [f"Yosys cannot read the design at {at}: {out.strip()[-1200:]}"]
    finally:
        shutil.rmtree(work, ignore_errors=True)


def check(sources, top, point, yosys=None):
    """Every rule at one point; a JSON-able dict with `passed`."""
    t0 = time.time()
    front, diags = slang_check(sources, top, point)
    back = yosys_check(sources, top, point, yosys)
    return {"passed": not front and not diags and not back, "point": dict(point),
            "findings": front + back, "diagnostics": diags,
            "seconds": round(time.time() - t0, 2)}


def point_text(point):
    """`N=8`, `W=5,P=11`, or `defaults` for a parameterless point."""
    return ",".join(f"{k}={v}" for k, v in dict(point).items()) or "defaults"


def check_points(sources, top, points, yosys=None):
    """Every rule at each of `points` in order (the checker gives the scoring point first, then the probe and backstop
    points), stopping at the first point that fails: a JSON-able dict with `passed`, `point` (the first point),
    `points` (each point checked: `point`, `passed`, `seconds`), `failed_point` (the point that failed, or None),
    `findings` and `diagnostics` (that point's), and the total `seconds`."""
    t0 = time.time()
    pts = [dict(p) for p in points] or [{}]
    rows, failed = [], None
    for p in pts:
        r = check(sources, top, p, yosys)
        rows.append({"point": r["point"], "passed": r["passed"], "seconds": r["seconds"]})
        if not r["passed"]:
            failed = r
            break
    return {"passed": failed is None, "point": pts[0], "points": rows,
            "failed_point": failed["point"] if failed else None,
            "findings": failed["findings"] if failed else [], "diagnostics": failed["diagnostics"] if failed else [],
            "seconds": round(time.time() - t0, 2)}


def task_point(task):
    return {k: int(v) for k, v in task["scoring"]["params"].items()}


# ---------------------------------------------------------------------------
# self test
# ---------------------------------------------------------------------------

SELFTEST = [
    # fixture (score/tests/fourstate/), top, the substrings its findings must contain
    ("ok_selects.sv", "ok_selects", []),
    ("undriven_mux.sv", "undriven_mux", ["is used but has no driver"]),
    ("partly_undriven_item.sv", "partly_undriven_item", ["is used but has no driver"]),
    ("oob_runtime.sv", "oob_runtime", ["3-bit index addresses 0..7, outside the declared "
                                       "range [3:0]"]),
    ("oob_partsel.sv", "oob_partsel", ["addresses 0..10, outside the declared range [7:0]",
                                       "addresses -3..3, outside the declared range [7:0]"]),
    ("oob_unpacked.sv", "oob_unpacked", ["addresses 0..7, outside the declared range [5:0]"]),
    # rule (d)'s write exception (txtask-v2 review, attack round 2's finding 3): an unsigned write
    # index past the top of the range passes; a signed one, and a read inside a written index, do not
    ("ok_oob_write.sv", "ok_oob_write", []),
    ("oob_signed_write.sv", "oob_signed_write",
     ["`t[i]`: a signed 2-bit index addresses -2..1, outside the declared range [3:0] (a signed "
      "write index", "`a[j]`: a 3-bit index addresses 0..7, outside the declared range [3:0] "
      "(an out-of-range read is x"]),
    # a constant index written with type/array query functions (the 2026-11-06 adversarial round, F3)
    ("ok_query_index.sv", "ok_query_index", []),
    ("query_runtime_index.sv", "query_runtime_index", ["run-time index in `v[$bits(v) - 1 - i]`"]),
    ("param_divzero.sv", "param_divzero", ["parameter `K`", "slang DivisionByZero"]),
    ("param_oob.sv", "param_oob", ["parameter `K2`", "slang IndexOOB"]),
    ("const_inline_x.sv", "const_inline_x", ["`(4'd3 / 4'd0)` is the constant",
                                             "`(4'd0 ** -1)` is the constant",
                                             "`f(2)` is the constant"]),
    ("const_oob_write.sv", "const_oob_write", ["slang IndexOOB"]),
    ("multi_driver.sv", "multi_driver", ["conflicting drivers"]),
    ("latch_block.sv", "latch_block", ["Latch inferred"]),
    # WP-PROC follow-up 3: a latch `proc` infers from `always @*` or `always_latch`; a complete `always @*` is none
    ("latch_star.sv", "latch_star", ["`proc` inferred a latch for `r`"]),
    ("latch_always_latch.sv", "latch_always_latch", ["`proc` inferred a latch for `r`"]),
    ("latch_star_two.sv", "latch_star_two", ["`proc` inferred a latch for `r`, `s`"]),
    ("ok_star_complete.sv", "ok_star_complete", []),
    ("loop_state.sv", "loop_state", ["found logic loop"]),
    ("loop_settling.sv", "loop_settling", ["found logic loop"]),
    # slang's ANALYSIS errors (decided 2026-11-01; score/slangdriver.py); the optional fourth field is the point
    ("analysis_two_always.sv", "analysis_two_always",
     ["slang analysis error MultipleAlwaysAssigns", "cannot be written to by any other process"]),
    ("analysis_mixed.sv", "analysis_mixed",
     ["slang analysis error MixedVarAssigns", "cannot mix continuous and procedural assignments"]),
    ("analysis_input.sv", "analysis_input",
     ["slang analysis error InputPortAssign", "cannot assign to input port 'a'"]),
    ("analysis_initial_comb.sv", "analysis_initial_comb",
     ["slang analysis error MultipleAlwaysAssigns"]),
    ("analysis_always_notime.sv", "analysis_always_notime",
     ["slang analysis error AlwaysWithoutTimingControl", "does not advance time"]),
    ("analysis_point.sv", "analysis_point", [], {"N": 4}),
    ("analysis_point.sv", "analysis_point", ["slang analysis error MultipleAlwaysAssigns"], {"N": 2}),
]


def selftest():
    d = os.path.join(HERE, "tests", "fourstate")
    failures = 0
    for f, top, want, *point in SELFTEST:
        res = check([os.path.join(d, f)], top, point[0] if point else {"N": 4})
        text = "\n".join(res["findings"] + res["diagnostics"])
        ok = (res["passed"] if not want else
              (not res["passed"] and all(w in text for w in want)))
        failures += not ok
        print(f"[{'ok' if ok else 'FAIL'}] {f}: {'pass' if res['passed'] else 'refused'}"
              f" ({res['seconds']}s){'' if ok else ': ' + text[:1500]}")
    print("selftest:", "PASS" if not failures else f"{failures} FAILED")
    return 1 if failures else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="*")
    ap.add_argument("--top")
    ap.add_argument("--point", help="NAME=VALUE[,NAME=VALUE] (default: the defaults)")
    ap.add_argument("--task", help="task directory: its top and scoring point")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if not args.sources:
        ap.error("no source files")
    if args.task:
        with open(os.path.join(args.task, "task.json")) as fh:
            task = json.load(fh)
        top, point = task["top"], task_point(task)
    else:
        if not args.top:
            ap.error("--top (or --task) is required")
        top = args.top
        point = ({kv.split("=")[0]: int(kv.split("=")[1]) for kv in args.point.split(",")}
                 if args.point else {})
    import srcgate
    work = tempfile.mkdtemp(prefix="svgolf-fourstate-gate-")
    try:
        canon = []
        for i, s in enumerate(args.sources):
            out = os.path.join(work, os.path.basename(s))
            try:
                srcgate.canonicalize(s, out, name=s)
            except srcgate.GateError as e:
                print(json.dumps({"passed": False, "source": str(e).splitlines()}, indent=2))
                return 1
            canon.append(out)
        try:
            res = check(canon, top, point)
        except InfraError as e:
            print(json.dumps({"passed": False, "infrastructure": str(e)}, indent=2))
            return 2
        def shown(x):
            for c, s in zip(canon, args.sources):
                x = x.replace(os.path.realpath(c), s).replace(c, s)
            return x
        for k in ("findings", "diagnostics"):
            res[k] = [shown(x) for x in res[k]]
    finally:
        shutil.rmtree(work, ignore_errors=True)
    print(json.dumps(res, indent=2, sort_keys=True))
    return 0 if res["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
