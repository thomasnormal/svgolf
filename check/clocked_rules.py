#!/usr/bin/env python3.12
"""svGolf: Python twins of txtask-v2's rules for CLOCKED tasks, before any Lean stage (check.py stage
`clocked_rules`).

The statement (`SvGolf/TaskSeq.lean`) and the pinned flow stay the authority; a twin here only refuses
early, with a clear message per construct, what the authority refuses anyway, and admits what it cannot
decide (the authority then decides: the proof, or the `score` stage). It reads the pinned extractor's
envelope (check/envelope.py), the tree `load_design_sv2` ingests: the probe sidecar's module at every
probe point (the task's probe points, the scoring point among them), or the envelope's top module when
there is no sidecar.

  RULE 3, NO X-CREATING CONSTRUCT (`XSafe`; txtask-v2, decided 2026-11-06: a Python twin of
  `xsafeB` refuses before the proof, the Lean rule stays the authority): the constructs listed at
  `xsafe_findings` below, each refused with its own message, at every probe point. Only constructs
  that ls-sv's lowering certainly turns into one `xsWidth` refuses are refused; the rest is the
  proof's (`tests/checker/test_xsafe_twin.py` runs the twin and `xsafeB` on the acceptance table's
  and the attacks' fixtures and shows they agree).

  NEVER-LOADED REGISTERS (txtask-v2, decided 2026-11-06): an ADVISORY (an early message, never a
  refusal): a register every write of which assigns it its own value (`u <= u`, under any conditions)
  and that something reads. Where the pinned Yosys removes such a flop while a read of it stays
  ("Handling D = Q ... (removing D path)") and resolves each read separately, the `score` stage
  refuses the design (check.py `never_loaded`, the scored run's own log: the authority, which also
  sees a load only under a condition that is never true or under an enable that is never active, and
  an array lane no write loads; the flow runs no fsm pass, which could re-implement a state register).
  Where the reads fold away first (`u ^ u`, or `t = u; t = 0`: the acceptance table's fixtures 0 and
  1), Yosys removes the flop as unread and the netlist is the design's, so the source alone cannot
  refuse. A register bit no write reaches is an undriven bit, which `fourstate` (e) refuses.

The walk is SOUND for refusals: it enters only code that is live at the point (the top module's
processes, and the bodies of `GenerateFor` blocks with at least one iteration whose bound reads no
enclosing genvar); it does not enter `GenerateIf` branches or instances (their liveness and parameters
are not evaluated here), so a construct there is left to the authority.

Usage:
  python3.12 check/clocked_rules.py ENVELOPE.json   # prints JSON {passed, findings, advisories, points, seconds}
Exit status 0 = passes, 1 = refused, 2 = usage error.
"""

import json
import os
import sys
import time

sys.dont_write_bytecode = True

PROCESS_KINDS = ("AlwaysPosedge", "AlwaysComb", "Assign")
ASSIGN_KINDS = ("BlockingAssign", "NonblockingAssign")


def sidecar_path(env_path):
    return (env_path[:-len(".json")] if env_path.endswith(".json") else env_path) + ".probes.json"


def modules_at_points(env_path):
    """[(point text, module JSON)]: the probe sidecar's points, else the envelope's top module ("defaults")."""
    side = sidecar_path(env_path)
    if os.path.exists(side):
        with open(side) as fh:
            d = json.load(fh)
        return [(",".join(f"{o['name']}={o['value']}" for o in p.get("overrides", [])) or "defaults", p["module"])
                for p in d.get("points", []) if p.get("module")]
    with open(env_path) as fh:
        d = json.load(fh)
    top = d.get("top")
    mods = [m for m in d["design"]["modules"] if m.get("name") == top] or d["design"]["modules"][:1]
    return [("defaults", mods[0])]


def mentions_genvar(node, genvars):
    if isinstance(node, dict):
        if node.get("kind") == "GenvarRef" and node.get("name") in genvars:
            return True
        return any(mentions_genvar(v, genvars) for v in node.values())
    if isinstance(node, list):
        return any(mentions_genvar(v, genvars) for v in node)
    return False


def live_processes(module):
    """The processes live at the module's point that this walk can see (module docstring)."""
    out = list(module.get("processes") or [])

    def gen(items, genvars):
        for it in items or []:
            k = it.get("kind")
            if k in PROCESS_KINDS:
                out.append(it)
            elif k == "GenerateFor":
                if (it.get("resolved_count") or 0) >= 1 and not mentions_genvar(it.get("bound"), genvars):
                    gen(it.get("body"), genvars | {it.get("genvar")})
    gen(module.get("generates"), frozenset())
    return out


def decls_of(module):
    """name -> declaration JSON (ports and variables/nets)."""
    return {d["name"]: d for d in list(module.get("ports") or []) + list(module.get("decls") or [])
            if isinstance(d, dict) and "name" in d}


def decl_width(decl):
    w = (decl or {}).get("width") or {}
    return w.get("resolved") if isinstance(w, dict) else None


def stmts(s):
    """Every statement node under `s` (itself included)."""
    if not isinstance(s, dict):
        return
    yield s
    k = s.get("kind")
    if k == "Block":
        for x in s.get("stmts") or []:
            yield from stmts(x)
    elif k == "If":
        yield from stmts(s.get("then"))
        yield from stmts(s.get("else"))
    elif k == "Case":
        for it in s.get("items") or []:
            yield from stmts(it.get("body"))
        yield from stmts(s.get("default"))
    elif k == "For":
        yield from stmts(s.get("body"))


# The system calls ls-sv's lowering evaluates to a constant from a declaration alone (Param.lean `evalInt`'s
# `.sysCall` arm: `$bits`/`$size`/`$high` of a declared signal; `instExpr2` lowers the call to a literal): their
# argument names a signal whose VALUE nothing reads (`sq[$bits(sq) - 1]` loads as a constant slice, `$bits(q) /
# $bits(q)` as a literal divisor: the 2026-11-06 adversarial round's finding F3, MEASURED `xsafeB` true). Any other
# argument is not folded (`evalInt` refuses it: an `Unsupported` node), and its names stay reads.
CONST_SYSCALLS = ("$bits", "$size", "$high")


def const_syscall(node):
    args = node.get("args") if isinstance(node, dict) else None
    return (node.get("kind") == "SysCall" and node.get("name") in CONST_SYSCALLS and isinstance(args, list)
            and len(args) == 1 and isinstance(args[0], dict) and args[0].get("kind") == "Ident")


def idents(node, out):
    """The signal names `node` reads (`Ident` and `ArraySel` names), into the set `out`; the argument of a call the
    lowering folds to a constant (`const_syscall`) is not a read."""
    if isinstance(node, dict):
        if const_syscall(node):
            return out
        if node.get("kind") in ("Ident", "ArraySel") and isinstance(node.get("name"), str):
            out.add(node["name"])
        for v in node.values():
            idents(v, out)
    elif isinstance(node, list):
        for v in node:
            idents(v, out)
    return out


# ---------------------------------------------------------------------------
# never-loaded registers (the source-level twin of check.py `never_loaded`)
# ---------------------------------------------------------------------------

def is_own_value(target, value, decls):
    """`target <= value` writes the whole signal its own value: `u <= u`, a same-width `Resize` of it, and the forms
    the pinned flow simplifies to it before opt_dff looks (the 2026-11-06 adversarial round: `u & u`, `u ^ 1'b0`,
    `u | 1'b0` and `u ? u : u` log "Handling D = Q", MEASURED; `u | u` and `u & '1` are the same identities)."""
    if not (isinstance(target, dict) and target.get("kind") == "Ident"):
        return False
    n, w = target.get("name"), decl_width(decls.get(target.get("name")))

    def lit(v, bit):
        return isinstance(v, dict) and (
            (v.get("kind") == "Literal" and set(str(v.get("bits", ""))) == {bit} and v.get("width") == w)
            or (v.get("kind") == "Fill" and str(v.get("bit")) == bit))

    def own(v):
        if not isinstance(v, dict):
            return False
        k = v.get("kind")
        if k == "Resize" and v.get("width") == w:
            return own(v.get("operand"))
        if k == "Ident":
            return v.get("name") == n
        if k == "Ternary":
            return own(v.get("then")) and own(v.get("else"))
        if k == "Binary" and v.get("op") in ("&", "|", "^"):
            a, b = v.get("left"), v.get("right")
            if v.get("op") in ("&", "|") and own(a) and own(b):
                return True
            ident = "1" if v.get("op") == "&" else "0"
            return (own(a) and lit(b, ident)) or (own(b) and lit(a, ident))
        return False
    return own(value)


def target_names(t):
    """The signals an assignment target writes (its select indices are reads, `target_reads`)."""
    if not isinstance(t, dict):
        return []
    k = t.get("kind")
    if k in ("Ident", "ArraySel"):
        return [t.get("name")]
    if k in ("BitSel", "PartSel"):
        return target_names(t.get("value"))
    if k == "ConcatTarget":
        return [n for p in t.get("parts") or [] for n in target_names(p)]
    return []


def target_reads(t, out):
    if isinstance(t, dict):
        k = t.get("kind")
        for key in {"BitSel": ("index",), "PartSel": ("msb", "lsb"), "ArraySel": ("indices", "part")}.get(k, ()):
            idents(t.get(key), out)
        if k in ("BitSel", "PartSel"):
            target_reads(t.get("value"), out)
        for p in t.get("parts") or [] if k == "ConcatTarget" else []:
            target_reads(p, out)
    return out


def never_loaded_findings(module):
    decls = decls_of(module)
    writes, comb_targets, reads = {}, set(), set()
    for p in live_processes(module):
        k = p.get("kind")
        if k == "Assign":
            comb_targets.update(target_names(p.get("target")))
            target_reads(p.get("target"), reads)
            idents(p.get("value"), reads)
            continue
        for s in stmts(p.get("body")):
            sk = s.get("kind")
            if sk in ASSIGN_KINDS:
                t, v = s.get("target"), s.get("value")
                target_reads(t, reads)
                if k != "AlwaysPosedge":
                    comb_targets.update(target_names(t))
                    idents(v, reads)
                elif isinstance(t, dict) and t.get("kind") == "Ident":
                    own = is_own_value(t, v, decls)
                    writes.setdefault(t["name"], []).append(own)
                    if not own:
                        idents(v, reads)
                else:
                    for n in target_names(t):        # a partial target: not a write of the register's own value
                        writes.setdefault(n, []).append(False)
                    idents(v, reads)
            elif sk == "If":
                idents(s.get("cond"), reads)
            elif sk == "Case":
                idents(s.get("subject"), reads)
                for it in s.get("items") or []:
                    idents(it.get("patterns"), reads)
            elif sk == "For":
                for key in ("init", "condition", "step"):
                    idents(s.get(key), reads)
    found = []
    for n, ws in sorted(writes.items()):
        if n and ws and all(ws) and n not in comb_targets and n in reads:
            found.append(f"register `{n}` is never loaded: every write assigns it its own value (`{n} <= {n}`). "
                         "Where the pinned Yosys removes its flip-flop while a read of it stays, it resolves each "
                         "read separately, and the score stage refuses the design (txtask-v2, decided 2026-11-06); "
                         "reset it, load it with a value other than its own, or remove it")
    return found


# ---------------------------------------------------------------------------
# rule 3, no x-creating construct (the twin of `xsafeB`, SvGolf/TaskSeq.lean): `xsafe_findings`
# ---------------------------------------------------------------------------
#
# `xsafeB` is a Boolean function of the LOADED design (`Design2`, after ls-sv's lowering, Param2.lean
# `instExpr2`); this twin refuses only what the lowering certainly turns into a construct `xsWidth` refuses,
# each read off the lowering (READ, LeanModels/Sv/Param2.lean):
#
#   division   `u/`, `s/`, `u%`, `s%` (and `/`, `%`) whose divisor reads a signal: the divisor is lowered by
#              `instDivOperand2`, never to a literal, so `constNZ` is false (`binW`);
#   power      `u**s`, `s**s` (a signed exponent) whose base reads a signal: the same, for the base;
#   signed index  a run-time bit/element select `v[i]`, read or written, whose index mentions a signal
#              declared signed: lowered to `Expr2.index`/`Lhs2.index`, whose names keep that signal, so
#              `unsignedIdx` is false;
#   index range  a run-time bit select `v[i]` (a plain signal `i` into a declared signal `v` with lsb 0 and
#              known element width `ew`) with `2^width(i) * ew > width(v)`: `xsWidth`'s `.index` case;
#   part select  a run-time indexed part select read `v[i +: W]` / `v[i -: W]`: `dynPartRead` pads the vector
#              with x literals (`LVec.xVec`), which `xsWidth` refuses;
#   x literal  a literal with an x or z digit (`'x`, `1'bz`, ...): `xsWidth (.lit v)` needs `allKnown`, except a
#              `casez`/`casex` item pattern that is the bare literal at the case's width (`patOK`; a pattern
#              narrower than an identifier subject is lowered under a `resize` and refused). The source gate
#              refuses every x digit and every x/z digit outside a casez/casex item before this.
#
# Everything else is left to the proof (`XSafe` is a conjunct of the statement): an operator at unequal widths
# (the lowering always fits the operands), a constant divisor written as an expression, an out-of-range constant
# select (`fourstate` (c)), an `Unsupported` node (the `design` stage).

DIV_OPS = {"u/", "s/", "u%", "s%", "/", "%"}
SIGNED_EXP_POW = {"u**s", "s**s"}


def show(e, n=60):
    """A short source-like text of an envelope expression, for messages."""
    def r(x):
        if not isinstance(x, dict):
            return "?"
        k = x.get("kind")
        if k in ("Ident", "ParamRef", "GenvarRef"):
            return x.get("name", "?")
        if k == "Literal":
            return f"{x.get('width')}'b{x.get('bits')}"
        if k == "Int":
            return str(x.get("value"))
        if k == "Fill":
            return "'" + str(x.get("bit"))
        if k == "Unary":
            return f"{x.get('op')}{r(x.get('operand'))}"
        if k == "Binary":
            op = x.get("op", "?")
            op = op[1:] if len(op) > 1 and op[0] in "us" and op[1] in "/%*<>" else op
            op = op[:-1] if op.endswith(("**s", "**u")) else op
            return f"({r(x.get('left'))} {op} {r(x.get('right'))})"
        if k == "Ternary":
            return f"({r(x.get('cond'))} ? {r(x.get('then'))} : {r(x.get('else'))})"
        if k == "Concat":
            return "{" + ", ".join(r(p) for p in x.get("parts") or []) + "}"
        if k in ("Resize", "SignedResize", "Squash2"):
            return r(x.get("operand"))
        if k == "Cast":
            return f"$signed({r(x.get('operand'))})" if x.get("signed") else f"$unsigned({r(x.get('operand'))})"
        if k == "BitSel":
            return f"{r(x.get('value'))}[{r(x.get('index'))}]"
        if k == "PartSel":
            return f"{r(x.get('value'))}[{r(x.get('msb'))}:{r(x.get('lsb'))}]"
        if k == "ArraySel":
            s = x.get("name", "?") + "".join(f"[{r(i)}]" for i in x.get("indices") or [])
            p = x.get("part")
            if p:
                sep = {"up": " +: ", "down": " -: "}.get(p.get("mode"), ":")
                s += f"[{r(p.get('left'))}{sep}{r(p.get('right'))}]"
            return s
        if k == "Repl":
            return "{" + r(x.get("count")) + "{" + r(x.get("operand")) + "}}"
        if k == "Reduce":
            return f"{x.get('op')}{r(x.get('operand'))}"
        if k == "SysCall":
            return f"{x.get('name')}(...)"
        return k or "?"
    s = r(e)
    return s if len(s) <= n else s[:n - 3] + "..."


def is_xz_literal(e):
    if not isinstance(e, dict):
        return False
    if e.get("kind") == "Literal":
        return any(c not in "01" for c in str(e.get("bits", "")))
    if e.get("kind") == "Fill":
        return str(e.get("bit")) not in ("0", "1")
    return False


def packed_dims(decl):
    w = (decl or {}).get("width") or {}
    return w.get("packed") if isinstance(w, dict) else None


def int_of(node):
    return node.get("value") if isinstance(node, dict) and node.get("kind") == "Int" else None


def elem_width(decl):
    """The element width of a bit/element select of `decl` (1 for a vector), when the lowering's `.index` reads
    the declared vector from bit 0 and it is known here: one packed dimension `[msb:0]` (or none), or inner
    dimensions that are literal integers; None otherwise."""
    dims = packed_dims(decl)
    if dims is None or (decl or {}).get("unpacked"):
        return None
    if not dims:
        return 1
    if int_of(dims[0].get("lsb")) != 0:
        return None
    ew = 1
    for d in dims[1:]:
        m, l = int_of(d.get("msb")), int_of(d.get("lsb"))
        if m is None or l is None:
            return None
        ew *= abs(m - l) + 1
    return ew


class XSafeTwin:
    def __init__(self, module):
        self.decls = decls_of(module)
        self.module = module
        self.found = []
        self.loop_vars = set()

    def signals(self, e):
        return {n for n in idents(e, set()) if n not in self.loop_vars}

    def signed_names(self, e):
        return sorted(n for n in self.signals(e) if (self.decls.get(n) or {}).get("signed") is True)

    def add(self, msg):
        if msg not in self.found:
            self.found.append(msg)

    def index(self, sel, idx, write):
        """A run-time bit/element select `sel` with index `idx` (read, or the target of a write)."""
        if not self.signals(idx):
            return
        signed = self.signed_names(idx)
        if signed:
            self.add(f"run-time index in `{show(sel)}`{' (a write)' if write else ''}: the index mentions "
                     + ", ".join(f"`{n}`" for n in signed) + ", declared signed; rule 3 (`XSafe`, `unsignedIdx`) "
                     "asks for an index that mentions no signal declared signed (IEEE 1800 reads a negative index "
                     "as out of range, ls-sv as an unsigned number: W5)")
            return
        base = sel.get("value") if sel.get("kind") == "BitSel" else None
        if (not write and isinstance(base, dict) and base.get("kind") == "Ident"
                and isinstance(idx, dict) and idx.get("kind") == "Ident"):
            vd, idd = self.decls.get(base.get("name")), self.decls.get(idx.get("name"))
            a, k, ew = decl_width(vd), decl_width(idd), elem_width(vd)
            if None not in (a, k, ew) and (2 ** k) * ew > a:
                self.add(f"run-time index in `{show(sel)}`: the {k}-bit index can address element "
                         f"{2 ** k - 1}, past the {a // ew if ew else a} elements of `{base.get('name')}`; an "
                         "out-of-range read is x, and rule 3 (`XSafe`) asks for an index whose every value is in "
                         "range (2^width(index) * element width <= width): pad the vector to a power of two or "
                         "narrow the index")

    def expr(self, e):
        """Walk a value-position expression."""
        if isinstance(e, list):
            for x in e:
                self.expr(x)
            return
        if not isinstance(e, dict):
            return
        k = e.get("kind")
        if is_xz_literal(e):
            self.add(f"an x/z literal `{show(e)}`: rule 3 (`XSafe`) admits an x or z digit only in a casez/casex "
                     "item pattern at the case's width (a z digit, and in casex an x digit, is a wildcard there; an "
                     "x digit of a casez item is not, and the source gate refuses it)")
            return
        if k == "Binary":
            op = e.get("op")
            if op in DIV_OPS and self.signals(e.get("right")):
                self.add(f"run-time {'division' if '/' in op else 'remainder'} `{show(e)}` by a divisor that "
                         "reads " + ", ".join(f"`{n}`" for n in sorted(self.signals(e.get("right"))))
                         + ": a divisor of 0 gives x, and rule 3 (`XSafe`, `binW`) admits only a divisor that is a "
                         "nonzero known constant")
            elif op in SIGNED_EXP_POW and self.signals(e.get("left")):
                self.add(f"power `{show(e)}` with a signed exponent and a base that reads a signal: 0 to a negative "
                         "power gives x, and rule 3 (`XSafe`, `binW`) admits a signed exponent only under a base "
                         "that is a nonzero known constant")
        elif k == "BitSel":
            self.index(e, e.get("index"), write=False)
        elif k == "ArraySel":
            p = e.get("part")
            if p and p.get("mode") in ("up", "down") and self.signals(p.get("left")):
                self.add(f"run-time indexed part select `{show(e)}`: ls-sv's lowering reads the window over the "
                         "vector padded with x bits (an out-of-range part reads x), which rule 3 (`XSafe`) refuses; "
                         "select through a packed array's element (`v[i]` of `logic [n-1:0][w-1:0] v`) or a shift")
        for key, v in e.items():
            if key != "kind" and isinstance(v, (dict, list)):
                self.expr(v)

    def target(self, t):
        if not isinstance(t, dict):
            return
        k = t.get("kind")
        if k == "BitSel":
            self.index(t, t.get("index"), write=True)
            self.expr(t.get("index"))
            self.target(t.get("value"))
        elif k == "PartSel":
            self.expr(t.get("msb"))
            self.expr(t.get("lsb"))
            self.target(t.get("value"))
        elif k == "ArraySel":
            self.expr(t.get("indices"))
            p = t.get("part") or {}
            self.expr(p.get("left"))
            self.expr(p.get("right"))
        elif k == "ConcatTarget":
            for p in t.get("parts") or []:
                self.target(p)

    def stmt(self, s):
        if not isinstance(s, dict):
            return
        k = s.get("kind")
        if k in ASSIGN_KINDS:
            self.target(s.get("target"))
            self.expr(s.get("value"))
        elif k == "If":
            self.expr(s.get("cond"))
            self.stmt(s.get("then"))
            self.stmt(s.get("else"))
        elif k == "Block":
            for x in s.get("stmts") or []:
                self.stmt(x)
        elif k == "Case":
            subj = s.get("subject")
            self.expr(subj)
            mode = s.get("match")
            sw = (decl_width(self.decls.get(subj.get("name")))
                  if isinstance(subj, dict) and subj.get("kind") == "Ident" else None)
            for it in s.get("items") or []:
                for p in it.get("patterns") or []:
                    if mode in ("casez", "casex") and is_xz_literal(p):
                        # the bare literal is admitted at the case's width (`patOK`); one narrower than an
                        # identifier subject is lowered under a resize (`fitExpr2`), which `xsWidth` refuses
                        if p.get("kind") == "Literal" and sw is not None and (p.get("width") or 0) < sw:
                            self.add(f"a {mode} item `{show(p)}` with an x/z digit, narrower than the subject "
                                     f"`{show(subj)}` ({sw} bits): ls-sv widens it under a resize, where rule 3 "
                                     "(`XSafe`, `patOK`) refuses the x/z digit; write the item at the subject's "
                                     "width")
                    else:
                        self.expr(p)
                self.stmt(it.get("body"))
            self.stmt(s.get("default"))
        elif k == "For":
            it = s.get("iterator")
            self.loop_vars.add(it)
            self.stmt(s.get("body"))

    def run(self):
        for p in live_processes(self.module):
            k = p.get("kind")
            if k == "Assign":
                self.target(p.get("target"))
                self.expr(p.get("value"))
            else:
                self.stmt(p.get("body"))
        return self.found


def xsafe_findings(module):
    return XSafeTwin(module).run()


# ---------------------------------------------------------------------------

def check(env_path):
    """Every twin at every point; a JSON-able dict with `passed`, `findings` (refusals) and `advisories` (early
    messages that refuse nothing). Each is reported once, with the points it holds at."""
    t0 = time.time()
    seen, advised, points = {}, {}, []
    for pt, mod in modules_at_points(env_path):
        points.append(pt)
        for f in xsafe_findings(mod):
            seen.setdefault(f, []).append(pt)
        for f in never_loaded_findings(mod):
            advised.setdefault(f, []).append(pt)

    def at(d):
        return [f"{f} (at {'; '.join(pts)})" for f, pts in d.items()]
    findings = at(seen)
    return {"passed": not findings, "findings": findings, "advisories": at(advised), "points": points,
            "seconds": round(time.time() - t0, 3)}


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 1:
        print(__doc__.split("Usage:")[1].strip(), file=sys.stderr)
        return 2
    res = check(argv[0])
    print(json.dumps(res, indent=2))
    return 0 if res["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
