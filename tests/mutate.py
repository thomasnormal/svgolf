#!/usr/bin/env python3.12
"""Mutant generator for svGolf references: standard mutation operators on a SystemVerilog design, located on
Slang's own syntax tree (pyslang, the frontend of the SV extractor), never on the source text.

    python3.12 tests/mutate.py SOURCE.sv --out DIR [--point N=1 --point N=8 ...] [--reset rst] [--json OUT]

Every mutant is ONE edit of the source (one node, or the two children of one node for a swap). The edit is
found by walking `pyslang.syntax.SyntaxTree` and taking the node's or token's source range; the replacement
text is built from the children's own source ranges. Nothing re-parses the source.

Operators (`op`; `ctx` says where the node is):

  ROR  a relational or equality operator replaced by each other one of == != < <= > >=
  AOR  an arithmetic operator replaced by each other one of + - *  (/ and % are never introduced: a run-time
       divisor can create an x, which the clocked rules refuse)
  BOR  a bitwise operator replaced by each other one of & | ^
  SOR  a shift operator replaced by each other one of << >> <<< >>>
  LOR  a logical operator replaced by the other one of && ||
  UOD  a unary ~ ! - deleted
  UOR  a unary ~ ! - replaced by each other one
  CRP  a constant changed: an unsized integer +1 and -1 (not below 0); a sized literal +1, -1 (mod 2^W)
       and each single-bit flip (W <= 16; else bits 0 and W-1); a fill '0 / '1 flipped whole, in bit 0
       and in its most significant bit (written so the value is the same at every context width:
       `1'b1`, `~1'b1`, `~('1 >> 1)`, `('1 >> 1)`). The ctx tells the kind: `param` (a parameter
       default), `index` (a declared range or a select: the index off-by-one), `shift` (a shift amount:
       the shift off-by-one), `expr`.
  NEG  the condition of an `if` or of a `? :` negated, `!(c)`
  SWP  the branches of an `if`/`else` or of a `? :` swapped (an `if` without `else`: `if (c) begin end
       else S`)
  SA0, SA1  a read of a declared signal (in a procedural block or a continuous assignment, not the
       target of an assignment, not an event control) replaced by '0 / '1
  DEL  one assignment statement replaced by the null statement `;`
  RST  the value an assignment in the reset branch (`if (<reset port>)` of an always_ff) gives, replaced by
       each other one of '0 '1 1'b1 ~('1 >> 1)
  OSW  the operands of a non-commutative binary operator swapped (- / % shifts < <= > >=)

Then the mutants are de-duplicated by text (the first operator to produce a text keeps it; the others are
recorded as `dup_of`) and ELABORATED by pyslang at every `--point` (parameter overrides of the top module):
a mutant with an error diagnostic at any point is dropped (`elaborates: false`, the first errors kept).

Output: DIR/<id>.sv for every kept mutant, and the manifest (`--json`, default DIR/mutants.json): the source's
sha256, the points, and one record per generated mutant: id, op, ctx, line, col, start, end (byte offsets
of the edit; a swap lists both), orig, repl, elaborates, errors, dup_of, file. Ids are stable for a source
and an operator set: m001, m002, ... in the order of the walk.

`rename_module(text, new)` (used by harnesses that instantiate a reference and a mutant side by side) renames
the first module declaration through the same syntax tree.

`python3.12 tests/mutate.py --selftest` checks the operators on a small fixed design.
"""
import argparse, hashlib, json, os, sys

import pyslang
from pyslang import ast, parsing, syntax

K = syntax.SyntaxKind

REL = {"EqualityExpression": "==", "InequalityExpression": "!=", "LessThanExpression": "<",
       "LessThanEqualExpression": "<=", "GreaterThanExpression": ">", "GreaterThanEqualExpression": ">="}
ARITH = {"AddExpression": "+", "SubtractExpression": "-", "MultiplyExpression": "*",
         "DivideExpression": "/", "ModExpression": "%"}
ARITH_TO = ("+", "-", "*")
BIT = {"BinaryAndExpression": "&", "BinaryOrExpression": "|", "BinaryXorExpression": "^",
       "BinaryXnorExpression": "~^"}
BIT_TO = ("&", "|", "^")
SHIFT = {"LogicalShiftLeftExpression": "<<", "LogicalShiftRightExpression": ">>",
         "ArithmeticShiftLeftExpression": "<<<", "ArithmeticShiftRightExpression": ">>>"}
LOGIC = {"LogicalAndExpression": "&&", "LogicalOrExpression": "||"}
NONCOMM = {"SubtractExpression", "DivideExpression", "ModExpression", "LessThanExpression",
           "LessThanEqualExpression", "GreaterThanExpression", "GreaterThanEqualExpression", *SHIFT}
UNARY = {"UnaryBitwiseNotExpression": "~", "UnaryLogicalNotExpression": "!", "UnaryMinusExpression": "-"}
ASSIGN = {"AssignmentExpression", "NonblockingAssignmentExpression"}
PROC = {"AlwaysCombBlock", "AlwaysFFBlock", "AlwaysBlock", "AlwaysLatchBlock", "InitialBlock",
        "ContinuousAssign", "FinalBlock"}
DECL = {"ParameterDeclaration", "DataDeclaration", "ImplicitAnsiPort", "ExplicitAnsiPort", "PortDeclaration",
        "NetDeclaration", "TypeParameterDeclaration", "LocalParameterDeclaration"}
RESET_VALUES = ("'0", "'1", "1'b1", "~('1 >> 1)")


def is_node(n):
    return n is not None and not isinstance(n, parsing.Token)


def rng(n):
    """The source range [start, end) of a node or a token."""
    if isinstance(n, parsing.Token):
        return n.range.start.offset, n.range.end.offset
    return n.sourceRange.start.offset, n.sourceRange.end.offset


def parse(text, name="design.sv"):
    return syntax.SyntaxTree.fromText(text, name)


def rename_module(text, new):
    """`text` with its first module declaration's name replaced by `new` (the name token's range)."""
    tree = parse(text)
    for m in walk_nodes(tree.root):
        if m.kind.name == "ModuleDeclaration":
            a, b = rng(m.header.name)
            return text[:a] + new + text[b:]
    raise ValueError("no module declaration")


def walk_nodes(n):
    if not is_node(n):
        return
    yield n
    for c in n:
        yield from walk_nodes(c)


class Gen:
    def __init__(self, text, reset=None):
        self.text, self.reset = text, reset
        self.tree = parse(text)
        self.out = []          # (op, ctx, [(start, end, repl)], orig)
        self.signals, self.params = set(), set()
        for n in walk_nodes(self.tree.root):
            k = n.kind.name
            if k == "Declarator" and is_node(n.parent):
                owner = n.parent
                while is_node(owner) and owner.kind.name not in DECL:
                    owner = owner.parent
                name = n.name.valueText
                if is_node(owner) and owner.kind.name in ("ParameterDeclaration", "LocalParameterDeclaration"):
                    self.params.add(name)
                else:
                    self.signals.add(name)

    def src(self, n):
        a, b = rng(n)
        return self.text[a:b]

    def add(self, op, ctx, edits, orig):
        self.out.append((op, ctx, edits, orig))

    def run(self):
        self.visit(self.tree.root, {"proc": False, "lhs": False, "event": False, "decl": False, "index": False,
                                    "shift": False, "param": False, "reset": False})
        return self.out

    def visit(self, n, c):
        if not is_node(n):
            return
        k = n.kind.name
        c = dict(c)
        if k in PROC:
            c["proc"] = True
        if k in DECL:
            c["decl"] = True
        if k in ("ParameterDeclaration", "LocalParameterDeclaration"):
            c["param"] = True
        if k in ("VariableDimension", "ElementSelect", "BitSelect", "SimpleRangeSelect"):
            c["index"] = True
        if k == "EventControlWithExpression" or k == "EventControl":
            c["event"] = True
        self.mutate(n, k, c)
        # the children, with the target of an assignment, a shift amount and the reset branch marked
        if k in ASSIGN:
            self.visit(n.left, dict(c, lhs=True))
            self.visit(n.right, c)
            return
        if k in SHIFT:
            self.visit(n.left, c)
            self.visit(n.right, dict(c, shift=True))
            return
        if k == "ConditionalStatement" and self.reset and self.is_reset_test(n.predicate):
            self.visit(n.predicate, c)
            self.visit(n.statement, dict(c, reset=True))
            if n.elseClause is not None:
                self.visit(n.elseClause, c)
            return
        for ch in n:
            self.visit(ch, c)

    def is_reset_test(self, pred):
        """Is the predicate of an `if` exactly the reset port (`if (rst)`)? On the node, not its text."""
        conds = list(pred.conditions)
        if len(conds) != 1 or conds[0].matchesClause is not None:
            return False
        e = conds[0].expr
        while e.kind.name == "ParenthesizedExpression":
            e = e.expression
        return e.kind.name == "IdentifierName" and e.identifier.valueText == self.reset

    def ctx_of(self, c):
        return ("param" if c["param"] else "index" if c["index"] else "shift" if c["shift"] else
                "decl" if c["decl"] else "expr")

    def mutate(self, n, k, c):
        expr = c["proc"] and not c["decl"] and not c["event"]
        # binary operators (in procedural code and continuous assignments)
        for table, to in ((REL, tuple(REL.values())), (ARITH, ARITH_TO), (BIT, BIT_TO),
                          (SHIFT, tuple(SHIFT.values())), (LOGIC, tuple(LOGIC.values()))):
            if k in table and expr:
                op = {id(REL): "ROR", id(ARITH): "AOR", id(BIT): "BOR", id(SHIFT): "SOR",
                      id(LOGIC): "LOR"}[id(table)]
                a, b = rng(n.operatorToken)
                for t in to:
                    if t != table[k]:
                        self.add(op, "expr", [(a, b, t)], table[k])
        if k in NONCOMM and expr:
            (la, lb), (ra, rb) = rng(n.left), rng(n.right)
            self.add("OSW", "expr", [(la, lb, self.src(n.right)), (ra, rb, self.src(n.left))],
                     self.src(n))
        # unary operators
        if k in UNARY and expr:
            a, b = rng(n.operatorToken)
            self.add("UOD", "expr", [(a, b, "")], UNARY[k])
            for t in UNARY.values():
                if t != UNARY[k]:
                    self.add("UOR", "expr", [(a, b, t)], UNARY[k])
        # constants
        if k == "IntegerLiteralExpression":
            v = n.literal.value
            a, b = rng(n)
            if isinstance(v, int) or hasattr(v, "__int__"):
                v = int(v)
                for w in (v + 1, v - 1):
                    if w >= 0:
                        self.add("CRP", self.ctx_of(c), [(a, b, str(w))], self.src(n))
        if k == "IntegerVectorExpression":
            self.sized(n, c)
        if k == "UnbasedUnsizedLiteralExpression":
            a, b = rng(n)
            lit = n.literal.rawText
            alts = {"'0": ("'1", "1'b1", "~('1 >> 1)"), "'1": ("'0", "~1'b1", "('1 >> 1)")}.get(lit, ())
            for t in alts:
                self.add("CRP", self.ctx_of(c), [(a, b, t)], lit)
        # conditions: negation and branch swap
        if k == "ConditionalStatement" and c["proc"]:
            a, b = rng(n.predicate)
            self.add("NEG", "if", [(a, b, f"!({self.src(n.predicate)})")], self.src(n.predicate))
            sa, sb = rng(n.statement)
            if n.elseClause is not None:
                ea, eb = rng(n.elseClause.clause)
                self.add("SWP", "if", [(sa, sb, self.src(n.elseClause.clause)), (ea, eb, self.src(n.statement))],
                         self.src(n))
            else:
                self.add("SWP", "if", [(sa, sb, "begin end else " + self.src(n.statement))], self.src(n))
        if k == "ConditionalExpression" and expr:
            a, b = rng(n.predicate)
            self.add("NEG", "?:", [(a, b, f"!({self.src(n.predicate)})")], self.src(n.predicate))
            (la, lb), (ra, rb) = rng(n.left), rng(n.right)
            self.add("SWP", "?:", [(la, lb, self.src(n.right)), (ra, rb, self.src(n.left))], self.src(n))
        # stuck-at on a read of a declared signal
        if k == "IdentifierName" and expr and not c["lhs"] and n.identifier.valueText in self.signals:
            a, b = rng(n)
            for op, t in (("SA0", "'0"), ("SA1", "'1")):
                self.add(op, "read", [(a, b, t)], self.src(n))
        # delete one assignment
        if k == "ExpressionStatement" and c["proc"] and n.expr.kind.name in ASSIGN:
            a, b = rng(n)
            self.add("DEL", "stmt", [(a, b, ";")], self.src(n))
        # the reset branch's values
        if k == "NonblockingAssignmentExpression" and c["reset"]:
            a, b = rng(n.right)
            for t in RESET_VALUES:
                if t != self.src(n.right):
                    self.add("RST", "reset", [(a, b, t)], self.src(n.right))

    def sized(self, n, c):
        """A sized literal W'bV: +1, -1 and single-bit flips, in its own base (x/z digits: skipped)."""
        size = n.size.value if n.size is not None else None
        base = n.base.rawText          # e.g. 'b, 'sd, 'h
        digits = n.value.rawText.replace("_", "")
        radix = {"b": 2, "o": 8, "d": 10, "h": 16}.get(base[-1].lower())
        try:
            w, v = int(size), int(digits, radix)
        except (TypeError, ValueError):
            return
        m = (1 << w) - 1
        bits = range(w) if w <= 16 else (0, w - 1)
        a, b = rng(n)
        seen = {v}
        for nv in [(v + 1) & m, (v - 1) & m] + [v ^ (1 << i) for i in bits]:
            if nv in seen:
                continue
            seen.add(nv)
            body = {2: format(nv, "b"), 8: format(nv, "o"), 10: str(nv), 16: format(nv, "x")}[radix]
            self.add("CRP", self.ctx_of(c), [(a, b, f"{w}{base}{body}")], self.src(n))


def apply(text, edits):
    out, pos = [], 0
    for a, b, t in sorted(edits):
        out += [text[pos:a], t]
        pos = b
    return "".join(out) + text[pos:]


def line_col(text, off):
    line = text.count("\n", 0, off) + 1
    return line, off - (text.rfind("\n", 0, off) + 1) + 1


def elaborate(text, point):
    """pyslang's error diagnostics for `text` with the top module's parameters overridden by `point`
    (a dict); [] when it elaborates."""
    tree = parse(text)
    co = ast.CompilationOptions()
    co.paramOverrides = [f"{k}={v}" for k, v in point.items()]
    comp = ast.Compilation(pyslang.Bag([co]))
    comp.addSyntaxTree(tree)
    eng = pyslang.DiagnosticEngine(comp.sourceManager)
    return [eng.formatMessage(d) for d in comp.getAllDiagnostics() if d.isError()]


def generate(text, points, reset=None):
    """The manifest records (module docstring) and the mutant texts: (records, {id: text})."""
    raw = Gen(text, reset).run()
    recs, texts, by_text = [], {}, {}
    for i, (op, ctx, edits, orig) in enumerate(raw, 1):
        mid = f"m{i:03d}"
        t = apply(text, edits)
        a = min(e[0] for e in edits)
        line, col = line_col(text, a)
        rec = {"id": mid, "op": op, "ctx": ctx, "line": line, "col": col,
               "start": [e[0] for e in edits], "end": [e[1] for e in edits], "orig": orig,
               "repl": edits[0][2] if len(edits) == 1 else [e[2] for e in edits]}
        if t == text:
            rec.update(elaborates=None, errors=["identical to the source"], dup_of=None, file=None)
        elif t in by_text:
            rec.update(elaborates=None, errors=[], dup_of=by_text[t], file=None)
        else:
            by_text[t] = mid
            errs = []
            for p in points:
                e = elaborate(t, p)
                if e:
                    errs.append(f"{','.join(f'{k}={v}' for k, v in p.items())}: " + "; ".join(e[:2]))
            rec.update(elaborates=not errs, errors=errs, dup_of=None, file=f"{mid}.sv" if not errs else None)
            if not errs:
                texts[mid] = t
        recs.append(rec)
    return recs, texts


def parse_point(s):
    out = {}
    for part in s.split(","):
        k, v = part.split("=")
        out[k.strip()] = int(v)
    return out


def selftest():
    src = ("module m #(parameter int N = 4) (input logic clk, rst, input logic [N-1:0] a, output logic [N-1:0] y);\n"
           "  logic [N-1:0] t;\n"
           "  always_comb t = (a != '0) ? a - 1'b1 : a << 1;\n"
           "  always_ff @(posedge clk) if (rst) y <= '0; else y <= t;\n"
           "endmodule\n")
    recs, texts = generate(src, [{"N": 1}, {"N": 4}], reset="rst")
    ops = {}
    for r in recs:
        ops.setdefault(r["op"], []).append(r)
    for op in ("ROR", "AOR", "SOR", "OSW", "CRP", "NEG", "SWP", "SA0", "SA1", "DEL", "RST"):
        assert op in ops, (op, sorted(ops))
    # the ternary's swap and the if's swap
    sw = [texts[r["id"]] for r in ops["SWP"] if r["file"]]
    assert any("? a << 1 : a - 1'b1" in t for t in sw), sw
    assert any("if (rst) y <= t; else y <= '0;" in t for t in sw), sw
    # no stuck-at on an assignment target or on the clock
    assert all(r["orig"] in ("a", "t", "rst") for r in ops["SA0"]), [r["orig"] for r in ops["SA0"]]
    # the reset value operator only in the reset branch
    assert all(r["start"][0] > src.index("if (rst)") and r["start"][0] < src.index("else y") for r in ops["RST"])
    # a parameter default is ctx param; a declared range's literal is ctx index; a shift amount is ctx shift
    ctxs = {(r["orig"], r["ctx"]) for r in ops["CRP"]}
    assert ("4", "param") in ctxs and ("1", "index") in ctxs and ("1", "shift") in ctxs, ctxs
    # every kept mutant elaborates, none is the source, texts are distinct
    assert all(r["elaborates"] for r in recs if r["file"])
    assert len(set(texts.values())) == len(texts) and src not in texts.values()
    # a mutant that does not elaborate is dropped: `y <= t` with t stuck at '0 is fine, a width error is not
    assert elaborate(src.replace("a - 1'b1", "a - "), {"N": 4})
    assert rename_module(src, "m2").startswith("module m2 #(")
    print(f"mutate.py: self-test ok ({len(recs)} generated, {len(texts)} kept)")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("source", nargs="?")
    ap.add_argument("--out")
    ap.add_argument("--point", action="append", default=[], help="parameter point, e.g. N=8 (repeatable)")
    ap.add_argument("--reset", help="the reset port (the RST operator's `if (<reset>)`)")
    ap.add_argument("--json", help="manifest path (default OUT/mutants.json)")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        selftest()
        return
    if not a.source or not a.out:
        ap.error("SOURCE and --out are required")
    with open(a.source) as fh:
        text = fh.read()
    points = [parse_point(p) for p in a.point] or [{}]
    recs, texts = generate(text, points, a.reset)
    os.makedirs(a.out, exist_ok=True)
    for mid, t in texts.items():
        with open(os.path.join(a.out, f"{mid}.sv"), "w") as fh:
            fh.write(t)
    man = {"source": os.path.basename(a.source), "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
           "pyslang": getattr(pyslang, "__version__", None), "points": points, "reset": a.reset,
           "generated": len(recs), "duplicates": sum(1 for r in recs if r["dup_of"]),
           "identical": sum(1 for r in recs if r["errors"] == ["identical to the source"]),
           "not_elaborating": sum(1 for r in recs if r["elaborates"] is False), "kept": len(texts),
           "mutants": recs}
    with open(a.json or os.path.join(a.out, "mutants.json"), "w") as fh:
        json.dump(man, fh, indent=1)
    print(f"{len(recs)} generated: {man['duplicates']} duplicates, {man['identical']} identical to the source, "
          f"{man['not_elaborating']} do not elaborate, {len(texts)} kept")


if __name__ == "__main__":
    main()
