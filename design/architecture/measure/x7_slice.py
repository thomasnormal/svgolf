#!/usr/bin/env python3.12
"""X7: the deterministic slicer. It turns two pinned ibex blocks into variants today's symbolic route can load,
and it records every change it makes, so that it is also a measurement of what the package tier has to cover.

    python3.12 -I x7_slice.py --src SRCROOT --files-tsv RB0_FILES_TSV --out OUTDIR [--slice ID]

SRCROOT holds the RB0 checkout layout (`SRCROOT/ibex/rtl/ibex_alu.sv`, ...). Every input file is checked against the
sha256 that the RB0 census pinned (svgolf/design/real-world-sv/rb0/files.tsv, lowRISC/ibex at f4515520c0); a
mismatch stops the run. The sliced files are written to OUTDIR only (a scratch directory, never this repository:
third-party code is not vendored), together with OUTDIR/<slice>/transforms.json, the per-file list of
transformations with their kind, their location in the pinned source and a count.

The sources are untrusted data. They are read as text and parsed by pyslang (enum values only); nothing in them is
executed. The transformations are exact: each one names its anchor text and the number of times it must match,
and the run stops if the pinned text does not match. The same inputs therefore always give the same bytes
(the output sha256 is recorded too).

Kinds (the table in X7.md counts these):
  generate-branch-fixed     a generate `if` on a parameter fixed at its default: the taken branch is kept, the
                            other is dropped (with every construct in it)
  param-fixed               a module parameter removed: the slice is at its default value
  package-import-removed    `import pkg::*` removed (the names it supplied are now localparams)
  package-enum-type-erased  a port or variable of a package enum type re-declared as the enum's base vector type
  package-enum-constant     a use of a package enum constant replaced by the sized literal of its value (count = uses)
  package-param-inlined     a use of a package parameter (not an enum) replaced by its sized literal
  param-comparison-folded   a comparison of a fixed parameter with a constant folded to its 1-bit value
  package-type-width        `$bits(pkg_type)` replaced by its value
  struct-member-cut         a read of a struct member replaced by a new input port (the slice's boundary)
  cut-to-input              a signal driven outside the slice becomes an input port
  internal-to-output        an internal signal of the slice becomes an output port (so the slice observes it)
  construct-rewrite         a construct today's extractor or recognizer refuses, rewritten into an equivalent
                            supported one (`inside` -> `||` of `==`; `unique case` -> `case` where provably equivalent)
  slice-range               a line range of the source kept verbatim in the slice
  refused-block-cut         an always_comb block today's recognizer refuses, removed (variant `@accepted` only)
  output-dropped            an output port whose only driver was cut, removed
"""
import argparse
import hashlib
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402

COMMIT = "f4515520c0045bb8ef1e72d46ed82499a6ac5f18"


class Slice:
    def __init__(self, sid, path, text):
        self.sid, self.path, self.text, self.log = sid, path, text, []

    def rec(self, kind, detail, line=None, count=1, **kw):
        e = {"kind": kind, "file": self.path, "detail": detail, "count": count}
        if line is not None:
            e["source_line"] = line
        e.update(kw)
        self.log.append(e)

    def line_of(self, anchor, src):
        i = src.find(anchor)
        return src[:i].count("\n") + 1 if i >= 0 else None

    def replace(self, kind, old, new, detail, n=1, src=None, **kw):
        c = self.text.count(old)
        if c != n:
            raise SystemExit("%s: anchor matched %d times, expected %d: %r" % (self.sid, c, n, old[:80]))
        line = self.line_of(old, src) if src is not None else None
        self.text = self.text.replace(old, new)
        self.rec(kind, detail, line=line, count=n, **kw)


def strip_comments(s):
    s = re.sub(r"/\*.*?\*/", lambda m: "\n" * m.group(0).count("\n"), s, flags=re.S)
    return re.sub(r"//[^\n]*", "", s)


def block_end(lines, i):
    """Index of the line holding the `end` that closes the LAST `begin` on line i (comments ignored; on line i
    everything before that `begin`, e.g. the `end` of `end else begin : B`, is skipped)."""
    depth = 0
    for k in range(i, len(lines)):
        code = re.sub(r"//.*", "", lines[k])
        if k == i:
            code = code[[m.start() for m in re.finditer(r"\bbegin\b", code)][-1]:]
        for tok in re.findall(r"\b(begin|end)\b", code):
            depth += 1 if tok == "begin" else -1
            if depth == 0:
                return k
    raise SystemExit("unbalanced begin/end from line %d" % (i + 1))


def fix_generate_if(sl, header, else_name, src):
    """`if (P) begin : A … end else begin : B … end` with P false at the fixed parameter value: keep B's body."""
    lines = sl.text.split("\n")
    hs = [k for k, l in enumerate(lines) if l.strip() == header]
    if len(hs) != 1:
        raise SystemExit("%s: generate header %r found %d times" % (sl.sid, header, len(hs)))
    h = hs[0]
    e1 = block_end(lines, h)
    if lines[e1].strip() != "end else begin : %s" % else_name:
        raise SystemExit("%s: expected `end else begin : %s` at line %d, got %r" % (sl.sid, else_name, e1 + 1, lines[e1]))
    e2 = block_end(lines, e1)
    if lines[e2].strip() != "end":
        raise SystemExit("%s: expected `end` at line %d" % (sl.sid, e2 + 1))
    dropped = lines[h + 1:e1]
    nested = [l.strip() for l in dropped if re.match(r"\s*(if|for)\s*\(.*\bbegin\s*:\s*\w+", l)
              or re.match(r"\s*end else begin\s*:\s*\w+", l)]
    body = [l[2:] if l.startswith("  ") else l for l in lines[e1 + 1:e2]]
    src_line = sl.line_of(header, src)
    sl.text = "\n".join(lines[:h] + ["  // [x7-slice] generate-branch-fixed: `%s` is false at the fixed value; "
                                     "branch `%s` kept, its body below" % (header, else_name)] + body + lines[e2 + 1:])
    sl.rec("generate-branch-fixed", "%s -> branch %s kept" % (header, else_name), line=src_line,
           dropped_lines=e1 - h - 1, nested_generate_blocks_dropped=nested)


def enum_info(pkg_file, names):
    comp, root, errs, sm = slang_env.compile_files([pkg_file])
    if errs:
        raise SystemExit("package does not compile: %s" % errs[:3])
    pkg = comp.getPackage("ibex_pkg")
    out = {}
    for nm in names:
        al = pkg.find(nm)
        t = al.targetType.type
        base = str(t.baseType)
        out[nm] = {"base": base, "width": t.bitWidth, "signed": t.isSigned, "pkg_line": sm.getLineNumber(al.location),
                   "members": [(m.name, sv_int(str(m.value))) for m in t]}
    return out


def sv_int(s):
    """A slang ConstantValue string (`7'h1f`, `2'b11`, `0`) as an int; x/z digits are refused."""
    if "'" not in s:
        return int(s)
    rest = s.split("'", 1)[1].lstrip("sS")
    base = {"b": 2, "o": 8, "d": 10, "h": 16}[rest[0].lower()]
    return int(rest[1:].replace("_", ""), base)


def sub_code(text, pattern, repl):
    """re.subn on the code of `text` only (comments untouched). Returns (text, count)."""
    parts = re.split(r"(//[^\n]*|/\*.*?\*/)", text, flags=re.S)
    n = 0
    for i in range(0, len(parts), 2):
        parts[i], k = re.subn(pattern, repl, parts[i])
        n += k
    return "".join(parts), n


def inline_enum(sl, info, enum):
    """Every use of a constant of package enum `enum` (a non-`integer` base) replaced by the sized literal of its
    value at the enum's width, `W'dV`. Exactly equivalent in every position: an enum constant of base `logic [W-1:0]`
    and the literal `W'dV` have the same width, signedness (unsigned), 4-state-ness and value. Today's route has no
    other spelling for it: enums are refused (`PDesign.summary`), localparams must be `int`/`integer`
    (`lpTypeOk`), and an `integer` constant compared with a narrower operand is a width conversion, also refused."""
    e = info[enum]
    if e["base"] == "integer" or e["signed"]:
        raise SystemExit("inline_enum: %s is %s" % (enum, e["base"]))
    names, uses = [], 0
    for n, v in e["members"]:
        if not 0 <= v < 2 ** e["width"]:
            raise SystemExit("%s = %d does not fit %s" % (n, v, e["base"]))
        sl.text, k = sub_code(sl.text, r"\b%s\b" % re.escape(n), "%d'd%d" % (e["width"], v))
        if k:
            names.append(n)
            uses += k
    sl.rec("package-enum-constant", "ibex_pkg::%s (%s): %d of %d constants named, %d uses inlined as `%d'dV`" %
           (enum, e["base"], len(names), len(e["members"]), uses, e["width"]), count=uses, constants=len(names),
           enum=enum, names=names, package_file="ibex/rtl/ibex_pkg.sv", package_line=e["pkg_line"])


def fold_param(sl, info, enum, param, value, src=None):
    """A parameter of the `integer` package enum `enum` fixed at `value`: every comparison `(param ==/!= CONST)`
    folded to its parenthesized 1-bit value (`(1'b0)`/`(1'b1)`: an equality is 1-bit unsigned, so this is exact). The run
    stops if `param` or a constant of `enum` is left anywhere in the code."""
    vals = dict(info[enum]["members"])
    seen = []

    def repl(m):
        c = m.group(3)
        if c not in vals:
            raise SystemExit("fold_param: %s is not a constant of %s" % (c, enum))
        r = (value == vals[c]) if m.group(2) == "==" else (value != vals[c])
        seen.append(m.group(0))
        return "(1'b1)" if r else "(1'b0)"   # the parentheses stay: they may be an `if`'s own
    sl.text, k = sub_code(sl.text, r"\(\s*(%s)\s*(==|!=)\s*(\w+)\s*\)" % re.escape(param), repl)
    left = [n for n in [param] + list(vals) if re.search(r"\b%s\b" % n, strip_comments(sl.text))]
    if left:
        raise SystemExit("fold_param: %s still named after folding" % left)
    sl.rec("param-comparison-folded", "%d comparisons of %s (fixed at %d) with ibex_pkg::%s constants folded to "
           "their 1-bit value" % (k, param, value, enum), count=k, forms=sorted(set(seen)))


def drop_unique(sl, scratch_dir):
    """`unique case (e)` -> `case (e)` exactly where that is equivalent: every case item is a constant (a parameter or
    an integer literal, after conversions), their values are pairwise distinct, and there is a `default`. Two distinct constants never both match
    one value under case equality, so no overlap violation can occur, and the `default` rules out the no-match
    violation; `unique` then changes nothing. Today's comb recognizer refuses `unique`/`priority case` (CombProc.lean,
    `caseStmt?`). Other `unique case` statements are left alone (and stay refused)."""
    from pyslang.ast import StatementKind, ExpressionKind, VisitAction, SymbolKind
    tmp = os.path.join(scratch_dir, "_drop_unique.sv")
    os.makedirs(scratch_dir, exist_ok=True)
    open(tmp, "w").write(sl.text)
    comp, root, errs, sm = slang_env.compile_files([tmp])
    if errs:
        raise SystemExit("%s: sliced text does not compile: %s" % (sl.sid, errs[:3]))
    hits, kept = [], []

    def visit(n):
        if getattr(n, "kind", None) == StatementKind.Case and str(n.check).endswith("Unique"):
            vals, ok = [], n.defaultCase is not None
            for it in n.items:
                for e in it.expressions:
                    while e.kind == ExpressionKind.Conversion:
                        e = e.operand
                    if e.kind == ExpressionKind.NamedValue and e.symbol.kind == SymbolKind.Parameter:
                        vals.append(str(e.symbol.value))
                    elif e.kind == ExpressionKind.IntegerLiteral:
                        vals.append(str(e.value))
                    else:
                        ok = False
            off = n.sourceRange.start.offset
            line = sl.text[:off].count("\n") + 1
            if ok and len(vals) == len(set(vals)):
                hits.append((off, line, len(vals)))
            else:
                kept.append(line)
        return VisitAction.Advance
    root.topInstances[0].body.visit(visit)
    os.remove(tmp)
    for off, line, n in sorted(hits, reverse=True):
        if sl.text[off:off + 12] != "unique case ":
            raise SystemExit("%s: no `unique case` at offset %d" % (sl.sid, off))
        sl.text = sl.text[:off] + sl.text[off + 7:]
    sl.rec("construct-rewrite", "`unique case` -> `case` where every item is a distinct constant and a `default` exists "
           "(exactly equivalent: no violation is possible)", count=len(hits), construct="unique-case",
           output_lines=sorted(l for _, l, _ in hits), unique_kept_output_lines=sorted(kept))


def cut_block(sl, anchor, writes, reason):
    """Remove the `always_comb` block that contains `anchor` (the block is refused by today's route)."""
    lines = sl.text.split("\n")
    ks = [k for k, l in enumerate(lines) if anchor in l]
    if len(ks) != 1:
        raise SystemExit("%s: block anchor %r found %d times" % (sl.sid, anchor, len(ks)))
    h = ks[0]
    while h >= 0 and lines[h].strip() != "always_comb begin":
        h -= 1
    e = block_end(lines, h)
    if not h < ks[0] <= e:
        raise SystemExit("%s: anchor %r not inside its block" % (sl.sid, anchor))
    sl.text = "\n".join(lines[:h] + ["  // [x7-slice] refused-block-cut: always_comb writing %s (%s)" %
                                      (", ".join(writes), reason)] + lines[e + 1:])
    sl.rec("refused-block-cut", "always_comb writing %s: %s" % (", ".join(writes), reason), lines=e - h + 1,
           writes=writes)


# ---------------------------------------------------------------------------------------------------------------
# ibex_alu, RV32B fixed to RV32BNone

def slice_alu(src_root, fix_branch=True, scratch=None):
    """`fix_branch=False` is the control variant `ibex_alu@pkgonly`: the package transformations only, the generate
    `if` on RV32B kept (it then tests a localparam), to measure what the package tier alone would buy."""
    path = "ibex/rtl/ibex_alu.sv"
    src = open(os.path.join(src_root, path)).read()
    sl = Slice("ibex_alu@rv32bnone" if fix_branch else "ibex_alu@pkgonly", path, src)
    info = enum_info(os.path.join(src_root, "ibex/rtl/ibex_pkg.sv"), ["alu_op_e", "rv32b_e"])
    if fix_branch:
        fix_generate_if(sl, "if (RV32B != RV32BNone) begin : g_alu_rvb", "g_no_alu_rvb", src)
    sl.replace("param-fixed", "module ibex_alu #(\n  parameter ibex_pkg::rv32b_e RV32B = ibex_pkg::RV32BNone\n) (",
               "module ibex_alu (", "RV32B (ibex_pkg::rv32b_e, default RV32BNone) removed; fixed at RV32BNone = 0",
               src=src)
    sl.replace("package-enum-type-erased", "  input  ibex_pkg::alu_op_e operator_i,",
               "  input  logic [6:0]        operator_i,", "port operator_i: ibex_pkg::alu_op_e -> logic [6:0]", src=src)
    sl.replace("package-import-removed", "  import ibex_pkg::*;\n", "", "import ibex_pkg::*", src=src)
    fold_param(sl, info, "rv32b_e", "RV32B", 0)
    inline_enum(sl, info, "alu_op_e")
    if fix_branch:
        sl.text, k = sub_code(sl.text, r"\$unsigned\((adder_in_a|adder_in_b)\)", r"\1")
        if k != 2:
            raise SystemExit("$unsigned anchor: %d" % k)
        sl.rec("construct-rewrite", "`$unsigned(x)` -> `x` for x = adder_in_a, adder_in_b (`logic [32:0]`, already "
               "unsigned: the call is the identity)", count=2, construct="$unsigned")
    sl.text = ("// [x7-slice] SLICED VARIANT of lowRISC/ibex %s rtl/ibex_alu.sv (RV32B fixed to RV32BNone%s).\n"
               "// Generated by svgolf/design/architecture/measure/x7_slice.py; transformations in transforms.json.\n"
               % (COMMIT, "" if fix_branch else "; package transformations only")) + sl.text
    if fix_branch:
        drop_unique(sl, scratch)
    return sl, "ibex_alu"


# The always_comb blocks of ibex_alu that today's comb recognizer refuses even after the edits above (MEASURED, the
# per-site verdicts of `siteOfP?` in the probe): several targets written in separate groups; after the first
# statement anything but `if (c) x = …;` overrides of the same target (a default, then a `case`; an `if … else`);
# `unique case (1'b1)` over signals, whose items can overlap.
ALU_REFUSED = [
    ("adder_op_a_shift1 = 1'b0;", ["adder_op_a_shift1", "adder_op_a_shift2", "adder_op_a_shift3", "adder_op_b_negate"],
     "defaults, then a case that overrides them"),
    ("multdiv_sel_i:     adder_in_a", ["adder_in_a"], "`unique case (1'b1)` over signals"),
    ("multdiv_sel_i:     adder_in_b", ["adder_in_b"], "`unique case (1'b1)` over signals"),
    ("shift_operand = 32'h8000_0000;", ["shift_operand", "shift_fill", "shift_result_ext", "shift_result",
                                        "unused_shift_result_ext", "shift_result_rev"],
     "an `if … else` after the first statement (and a procedural `for`)"),
    ("bwlogic_or:  bwlogic_result", ["bwlogic_result"], "`unique case (1'b1)` over signals"),
    ("result_o   = '0;", ["result_o"], "a default, then a case that overrides it"),
]


def slice_alu_accepted(src_root, scratch):
    """`ibex_alu@accepted`: `ibex_alu@rv32bnone` with the refused always_comb blocks cut. Of what they write, only
    `adder_in_a`/`adder_in_b` is read by a remaining site; those become input ports. `result_o` loses its driver and is
    dropped from the ports. The other variables stay declared, undriven and unread."""
    sl, top = slice_alu(src_root, scratch=scratch)
    sl.sid = "ibex_alu@accepted"
    for anchor, writes, reason in ALU_REFUSED:
        cut_block(sl, anchor, writes, reason)
    for old, new in (("  logic [32:0] adder_in_a, adder_in_b;\n", ""),
                     ("  input  logic              multdiv_sel_i,\n",
                      "  input  logic              multdiv_sel_i,\n  input  logic [32:0]       adder_in_a,\n"
                      "  input  logic [32:0]       adder_in_b,\n")):
        if sl.text.count(old) != 1:
            raise SystemExit("accepted: anchor %r" % old)
        sl.text = sl.text.replace(old, new)
    sl.rec("cut-to-input", "adder_in_a, adder_in_b (written by cut blocks, read by `assign adder_result_ext_o`) -> "
           "input logic [32:0]", count=2)
    sl.replace("output-dropped", "  output logic [31:0]       result_o,\n", "",
               "result_o: its only driver (the result mux) is cut")
    sl.text = sl.text.replace("(RV32B fixed to RV32BNone).\n", "(RV32B fixed to RV32BNone; the always_comb blocks "
                              "today's route refuses cut).\n", 1)
    return sl, top


# ---------------------------------------------------------------------------------------------------------------
# ibex_cs_registers: the CSR operation and access-check logic, with its boundary cut to ports

CSR_KEEP = [(394, 404), (998, 1023)]


def slice_csr(src_root, scratch=None):
    path = "ibex/rtl/ibex_cs_registers.sv"
    src = open(os.path.join(src_root, path)).read()
    lines = src.split("\n")
    sl = Slice("ibex_cs_registers@csrop", path, "")
    info = enum_info(os.path.join(src_root, "ibex/rtl/ibex_pkg.sv"), ["csr_op_e", "base_isa_e"])
    kept = []
    for a, b in CSR_KEEP:
        kept += ["  // [x7-slice] slice-range: source lines %d-%d" % (a, b)] + lines[a - 1:b]
        sl.rec("slice-range", "lines %d-%d verbatim" % (a, b), line=a, lines=b - a + 1)
    sl.text = "\n".join(kept)
    # the transformations inside the kept text
    sl.replace("package-type-width", "  logic [$bits(csr_num_e)-1:0] csr_addr;", "  logic [11:0] csr_addr;",
               "$bits(ibex_pkg::csr_num_e) = 12", src=src)
    sl.replace("construct-rewrite", "(csr_op_i inside {CSR_OP_WRITE, CSR_OP_SET, CSR_OP_CLEAR})",
               "((csr_op_i == CSR_OP_WRITE) || (csr_op_i == CSR_OP_SET) || (csr_op_i == CSR_OP_CLEAR))",
               "`inside` on a value set -> `||` of `==` (4-state equal: `inside` compares integral operands with `==?`, "
               "which agrees with `==` when the set member has no x/z bit, as these constants have none; and `inside` "
               "is 1 on a match, 0 when all are 0, x otherwise, which is the `||` of the comparisons)",
               src=src, construct="InsideExpression")
    sl.replace("struct-member-cut", "pcc_cap_q.perms.SR", "pcc_cap_perms_sr",
               "pcc_cap_q.perms.SR (ibex_cheriot_pkg::decoded_cap_t member) -> input pcc_cap_perms_sr", src=src)
    body = sl.text
    # the module header: original ports used, then the cut, then the outputs
    ports = [
        ("input ", "logic", "csr_access_i", None),
        ("input ", "logic [11:0]", "csr_addr_i", "package-enum-type-erased"),
        ("input ", "logic [31:0]", "csr_wdata_i", None),
        ("input ", "logic [1:0]", "csr_op_i", "package-enum-type-erased"),
        ("input ", "logic", "csr_op_en_i", None),
        ("input ", "logic [3:0]", "cheriot_enable_i", "package-type-alias-erased"),
        ("input ", "logic", "debug_mode_i", None),
        ("input ", "logic [1:0]", "priv_lvl_q", "cut-to-input"),
        ("input ", "logic", "illegal_csr", "cut-to-input"),
        ("input ", "logic", "dbg_csr", "cut-to-input"),
        ("input ", "logic [31:0]", "csr_rdata_int", "cut-to-input"),
        ("input ", "logic", "pcc_cap_perms_sr", None),
        ("output", "logic [31:0]", "csr_rdata_o", None),
        ("output", "logic", "illegal_csr_insn_o", None),
        ("output", "logic [31:0]", "csr_wdata_int", "internal-to-output"),
        ("output", "logic", "csr_we_int", "internal-to-output"),
    ]
    detail = {
        "csr_addr_i": "port csr_addr_i: ibex_pkg::csr_num_e -> logic [11:0]",
        "csr_op_i": "port csr_op_i: ibex_pkg::csr_op_e -> logic [1:0]",
        "cheriot_enable_i": "port cheriot_enable_i: ibex_pkg::ibex_mubi_t -> logic [3:0]",
        "priv_lvl_q": "priv_lvl_q (ibex_pkg::priv_lvl_e register, always_ff at source line 985) -> input logic [1:0]",
        "illegal_csr": "illegal_csr (driven by the CSR read mux, source lines 413-715) -> input",
        "dbg_csr": "dbg_csr (driven by the CSR read mux) -> input",
        "csr_rdata_int": "csr_rdata_int (driven by the CSR read mux) -> input",
        "csr_wdata_int": "csr_wdata_int (read by the CSR write logic and the ibex_csr instances outside the slice) -> output",
        "csr_we_int": "csr_we_int (read by the CSR write logic outside the slice) -> output",
    }
    anchor = {"csr_addr_i": "ibex_pkg::csr_num_e   csr_addr_i", "csr_op_i": "ibex_pkg::csr_op_e    csr_op_i",
              "cheriot_enable_i": "ibex_mubi_t           cheriot_enable_i", "priv_lvl_q": "priv_lvl_e    priv_lvl_q",
              "illegal_csr": "logic        illegal_csr;", "dbg_csr": "logic        dbg_csr;",
              "csr_rdata_int": "logic [31:0] csr_rdata_int;", "csr_wdata_int": "logic [31:0] csr_wdata_int;",
              "csr_we_int": "logic        csr_we_int;"}
    for d, ty, nm, kind in ports:
        if kind == "package-type-alias-erased":
            sl.rec("package-enum-type-erased", detail[nm], line=sl.line_of(anchor[nm], src),
                   note="a package typedef of a packed vector, not an enum")
        elif kind:
            sl.rec(kind, detail[nm], line=sl.line_of(anchor[nm], src))
    hdr = ["// [x7-slice] SLICED VARIANT of lowRISC/ibex %s rtl/ibex_cs_registers.sv: the CSR operation and" % COMMIT,
           "// access-check logic (source lines %s), its boundary cut to ports." % ", ".join("%d-%d" % r for r in CSR_KEEP),
           "// Generated by svgolf/design/architecture/measure/x7_slice.py; transformations in transforms.json.",
           "module ibex_cs_registers_csrop ("]
    hdr += ["  %s %-12s %s%s" % (d, ty, nm, "," if k < len(ports) - 1 else "") for k, (d, ty, nm, _) in enumerate(ports)]
    hdr += [");"]
    sl.rec("param-fixed", "BaseIsa (ibex_pkg::base_isa_e, default BaseIsaRV32I) not carried over; fixed at "
           "BaseIsaRV32I = 0", line=sl.line_of("parameter base_isa_e              BaseIsa", src))
    decl = []
    sl.rec("package-import-removed", "module header `import ibex_pkg::*, ibex_cheriot_pkg::*;`", line=31, count=2)
    # the slice's internal declarations, verbatim from the source (lines 319-354)
    want = ["mhpmcounter_idx", "csr_wr", "illegal_csr_priv", "illegal_csr_dbg", "illegal_csr_write", "unused_csr_addr"]
    for nm in want:
        hits = [l for l in lines[318:355] if re.search(r"\b%s\b\s*;" % nm, l)]
        if len(hits) != 1:
            raise SystemExit("declaration of %s: %d hits" % (nm, len(hits)))
        decl.append(hits[0])
    sl.text = "\n".join(hdr + decl + [sl.text, "", "endmodule", ""])
    fold_param(sl, info, "base_isa_e", "BaseIsa", 0)
    inline_enum(sl, info, "csr_op_e")
    sl.text, k = sub_code(sl.text, r"\bIbexMuBiOn\b", "4'b0101")
    sl.rec("package-param-inlined", "ibex_pkg::IbexMuBiOn (ibex_mubi_t = logic [3:0], 4'b0101): %d use(s) inlined as "
           "`4'b0101` (same width, signedness and value)" % k, count=k,
           line=sl.line_of("(cheriot_enable_i != IbexMuBiOn)\n       | debug_mode_i", src))
    drop_unique(sl, scratch)
    return sl, "ibex_cs_registers_csrop"


ALU_IN = ["ibex/rtl/ibex_alu.sv", "ibex/rtl/ibex_pkg.sv"]
SLICES = {"ibex_alu@rv32bnone": (lambda r, t: slice_alu(r, scratch=t), ALU_IN),
          "ibex_alu@pkgonly": (lambda r, t: slice_alu(r, fix_branch=False, scratch=t), ALU_IN),
          "ibex_alu@accepted": (slice_alu_accepted, ALU_IN),
          "ibex_cs_registers@csrop": (lambda r, t: slice_csr(r, scratch=t),
                                      ["ibex/rtl/ibex_cs_registers.sv", "ibex/rtl/ibex_pkg.sv"])}


def pinned(tsv):
    pins = {}
    for l in open(tsv):
        f = l.rstrip("\n").split("\t")
        if len(f) >= 5 and f[0] == "ibex":
            pins["ibex/" + f[3]] = (f[2], f[4])
    return pins


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--files-tsv", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--slice")
    a = ap.parse_args()
    pins = pinned(a.files_tsv)
    for sid, (fn, inputs) in SLICES.items():
        if a.slice and sid != a.slice:
            continue
        srcs = {}
        for p in inputs:
            commit, sha = pins[p]
            got = hashlib.sha256(open(os.path.join(a.src, p), "rb").read()).hexdigest()
            if commit != COMMIT or got != sha:
                raise SystemExit("%s: not the pinned file (commit %s, sha256 %s, want %s)" % (p, commit, got, sha))
            srcs[p] = sha
        sl, top = fn(a.src, a.out)
        d = os.path.join(a.out, sid)
        os.makedirs(d, exist_ok=True)
        out = os.path.join(d, top + ".sv")
        open(out, "w").write(sl.text)
        kinds = {}
        for e in sl.log:
            kinds[e["kind"]] = kinds.get(e["kind"], 0) + e["count"]
        rec = {"slice": sid, "top": top, "repo": "lowRISC/ibex", "commit": COMMIT, "inputs_sha256": srcs,
               "output": os.path.basename(out), "output_sha256": hashlib.sha256(sl.text.encode()).hexdigest(),
               "output_lines": sl.text.count("\n"), "by_kind": kinds, "transforms": sl.log}
        json.dump(rec, open(os.path.join(d, "transforms.json"), "w"), indent=1)
        print(sid, "->", out, kinds)


if __name__ == "__main__":
    main()
