#!/usr/bin/env python3.12
"""svGolf source gate: make the extractor (slang) and Yosys read ONE program.

The proof is about the design that lean-surfaces' extractor reads (through
slang); the score is about the design that Yosys's `read_verilog -sv` reads.
Those must be the same program, or a player proves one circuit and gets
scored on another. Handing both tools the same FILE is not enough, because
each tool reads things into a file that the other does not:

* the PREPROCESSOR: Yosys always defines the macros `SYNTHESIS` and `YOSYS`
  (`read_verilog -nosynthesis` drops only the first), slang defines neither,
  so `` `ifdef SYNTHESIS assign y = '0; `else assign y = a & b; `endif ``
  is proved as `a & b` and scored as a constant (0 GE). Any directive,
  macro, `` `include `` or `` `line `` is a second way to the same trick;
* COMMENTS: Yosys honours `// synopsys translate_off` (it skips the code up
  to `translate_on`) and `// synopsys full_case` / `parallel_case`; slang
  ignores comments;
* ATTRIBUTES: Yosys gives `(* full_case *)`, `(* parallel_case *)`,
  `(* nosync *)`, `(* keep_hierarchy *)`, `(* blackbox *)` and many more a
  synthesis meaning, and `{* ... *}` sets default attributes; slang (and
  IEEE 1800 simulation) give attributes no meaning;
* `unique` / `unique0` / `priority` case qualifiers: Yosys's parser turns
  them into exactly the `full_case` / `parallel_case` attributes, i.e. it
  treats "no item matches" (and, for `unique`, "several items match") as a
  synthesis don't-care. ls-sv runs them as IEEE 1800 does: the first
  matching arm, or nothing, with the violation a simulator warning only
  (`LeanModels/Sv/Sem2.lean`). A `unique case (1'b1) (a[0] & ~a[0]): y = '0;
  endcase` after `y = a & b` is `a & b` to ls-sv and the constant 0 to Yosys
  (0 GE, measured with the pinned script). These keywords are part of the
  language, not tool directives, so rejecting them is a policy decision:
  remove the entries of `SYNTH_QUALIFIERS` to admit them, and leave such a
  violation to the checker's post-synthesis check (`check/postsynth.py`),
  which catches it where its vectors reach it (measured on
  `tests/_example/attacks/`: a qualifier that never matches on every
  vector, overlapping items on a quarter of them, an overlap hidden behind
  constant comparisons only through the harvested vectors).

The gate therefore:

1. REJECTS (with `file:line:col`): every compiler directive except
   `` `timescale `` and `` `default_nettype none|wire `` (so: no macro, no
   conditional, no include); every attribute `(* ... *)` and every `{*` /
   `*}`; every `unique` / `unique0` / `priority` keyword; every comment that
   Yosys would read as a pragma (`synopsys` / `synthesis` / `pragma` at the
   start, or `translate_off` / `translate_on` / `full_case` /
   `parallel_case` anywhere); non-ASCII or control characters outside
   comments; text that is not UTF-8; and every x/z literal digit outside a
   casez/casex item wildcard (item 4 below); and every use of the host
   (item 5 below).
2. STRIPS every comment (replaced by spaces, newlines kept, so every line
   and column number stays valid) and returns this CANONICAL text. Callers
   hand the canonical text, not the submitted file, to the extractor, the
   banlist and Yosys. Rejecting pragma comments is a courtesy (the player
   learns that Yosys would have read their file differently); STRIPPING is
   the guarantee, and it does not depend on knowing every comment form that
   Yosys recognizes.
3. VALIDATES the canonical text with slang: it has no comment, and its token
   sequence is identical to the submitted file's (so stripping removed
   comments and nothing else), and no `//` or `/*` survives anywhere (not
   even inside a string or an escaped identifier, where Yosys's lexer might
   see a comment that slang does not).
   (Items 4 to 7 below are further refusals; 6 applies to clocked tasks only.)

4. REJECTS every `x`, `z` or `?` digit in a literal (`1'bz`, `4'b10x0`,
   `8'hz?`, `'x`, `'z`), except the wildcard digits of a `casez` item (`z`,
   `?`) and of a `casex` item (`x`, `z`, `?`), where both tools read them
   as "matches anything". Everywhere else the two tools give such a bit
   different meanings: ls-sv (like IEEE 1800 simulation) computes with an
   unknown value, so a case item or an `==` operand with a `z` bit never
   matches a known input and `if (x)` takes the else branch, while Yosys
   reads an x/z bit as a synthesis don't-care, drops it from comparisons
   (measured: the complementary items `2'b0z` and `2'b1z` on `{a[0], cin}`
   together match EVERY input in Yosys, and none in ls-sv) and resolves an
   unknown value freely. A proof would then be about one circuit and the
   score about another, the difference confined to wherever the player
   likes; sampling (the post-synthesis check) misses a rare one. The
   refusal is lexical and exact; x values that arise WITHOUT a literal
   (a parameter computed as `1/0`, an out-of-range select, an undriven
   net) are the checker's `fourstate` stage (`score/fourstate.py`), which
   elaborates the design at the scoring point.

5. REJECTS every construct that reaches the HOST the checker runs on
   (P-NO-HOST-ACCESS): the checker runs untrusted text on the organizer's
   machine, and Yosys's `read_verilog` really does open the file of a
   `$readmemh` / `$readmemb` while it reads the design (measured with the
   pinned Yosys 0.53: the file's contents become the memory's initial value, so
   the same submitted text scores 9.331 GE with one host file and 0 GE with
   another, and a file that does not exist is an error), a hidden salt or
   oracle file on the organizer's machine could be read into the netlist and
   leaked through the score. The proof (ls-sv) never sees the file, so the
   proved and the scored circuits would also differ. The refused constructs
   (`HOST_FAMILIES`, a data table: one row per family, with the LRM clause that
   defines it and its system names): the memory-file tasks (`$readmem*`,
   `$writemem*`); the file I/O family (`$fopen` ... `$ferror`, LRM 21.3); process
   and environment access (`$system`, `$test$plusargs`, `$value$plusargs`,
   `$getenv`); wave and dump writers (`$dumpfile` ... `$dumpports*`, and the
   vendor families in `HOST_SYSTEM_PREFIXES`); the coverage database tasks
   (`$coverage_save` ...); `$sdf_annotate`; the file-bound optional tasks of
   Annex D (`$input`, `$log`, `$save` ...); and DPI, native code (`import
   "DPI-C"`, `export "DPI-C"`, LRM 35). They are found in slang's SYNTAX TREE of
   the submitted text, token by token, not by a regex over the characters: a
   comment or a string literal that merely names one is not a finding, and
   neither a task nor a function body, a generate branch that the scoring point
   does not elaborate, a module the top never instantiates nor a parameter
   initializer is exempt (the gate looks at the text, not at the elaborated
   design: Yosys elaborates a different subset than slang does).
   An ESCAPED identifier that begins with `$` (`\\$readmemh `) is refused
   whatever its name: Yosys's lexer gives `\\$readmemh` the very same name as the
   system task `$readmemh` and executes it, while slang reads an ordinary
   identifier (measured: a user function `\\$clog2` is the user's for slang, the
   builtin `$clog2` for Yosys, so even an ADMITTED system name can be given two
   meanings that way). The console and simulation-control tasks
   (`$display`, `$write`, `$strobe`, `$monitor`, `$finish`, `$stop`, `$error`,
   `$warning`, `$info`, `$fatal`, `$time`, ...) and the pure system functions
   (`$clog2`, `$bits`, `$signed`, `$countones`, ...) touch no host resource and
   are not touched by the gate. An unknown system name (a vendor PLI task) is
   not refused here either: slang gives it no meaning and the pinned Yosys
   stops at it (`Can't resolve task name`).

6. For a CLOCKED task (`gate_text(..., clock=<port>)`, `--clock`; check.py passes the task's
   `clock` for every clocked kind, `seq-family`, `tx-family` and `stream-family`; PLAN4 Gate 2 step 2)
   it also REJECTS what
   the clocked profile does not run (`clocked_findings`): an edge process that is not exactly
   `always_ff @(posedge <clock>)` (a second clock, `negedge`/`edge`, a second event such as an
   asynchronous reset, `iff`); any other event control, any delay, `wait`, `fork`; `initial`,
   `final`, `always_latch`; a blocking assignment (`=`, `+=`, `++`, ...) in an `always_ff` body,
   with ONE exception; an initializer on a variable's or a variable port's declaration.
   Combinational feedback stays with the loader's checks.
   The purpose of the blocking rule is the clock-step profile's (PLAN4 Gate 1,
   `Stmt2.nbaOnly` in LeanModels/Sv/Seq2Cycle.lean, `ffOnlyProfileB` in SeqProfile.lean): every
   register updates from the same pre-edge state, so a blocking write that another process
   could see is a race. The exception is the HEADER of a procedural `for` loop, which item 7
   judges for every process (it admits exactly one blocking write there: the step on the
   iterator the header itself declares, `for (int i = 0; i < N; i++)`): no other process can
   name that iterator, and E expands the loop at instantiation (Param2.lean `instStmt2
   .forLoop`: one body copy per value `forValues2` computes from the header), so the iterator
   never reaches `Stmt2`. Still REFUSED here: a blocking write to anything declared outside
   the `always_ff` (a module variable, a port); ANY write (`=` or `<=`) to a loop iterator
   outside its header, in the body in particular (in SystemVerilog it changes the iteration
   sequence, while the expansion computes its values from the header alone); and block-local
   temporaries (`begin logic t; t = a + b; q <= t; end`): the clock-step profile does not
   admit them yet.

7. For EVERY procedural `for` loop (in `always_ff`, `always_comb`, `always @*`, `initial`, a
   function or a task; generate loops are not procedural) it REFUSES every header but one
   narrow shape, matched structurally on slang's syntax tree (`loop_findings`). This is a
   STOPGAP for three mis-models of procedural `for` loops in ls-sv's extractor/E, measured by
   an adversarial probe set against Yosys and a simulator, until the ls-sv fix lands: (a) the
   condition is evaluated as a signed comparison where SystemVerilog compares unsigned
   (`i < 2'd2` from `i = -1`, or an unsigned or packed-typed parameter as the bound: E runs
   the body, the tools do not); (b) the iterator is bound by NAME in the parameter table, so
   an iterator spelled like a module localparam captures that localparam inside an inlined
   function; (c) the iterator's declared type is ignored (a `bit [2:0]` iterator wraps in
   SystemVerilog, not in E). Each finding names its reason and the defect it stands in for.
   Admitted, and nothing else:
   * ONE iterator, DECLARED in the header (slang's `ForVariableDeclaration`) as `int` or
     `integer` (optionally `signed`, `var`), with an initial value: not `bit`/`logic`/`byte`/
     `shortint`/`longint`, nothing packed or `unsigned`, and not a variable declared elsewhere
     (`integer i; ... for (i = 0; ...)`, at module, block or function scope);
   * an iterator name that NO name declared at module scope has (parameters, localparams,
     ports, nets, variables, functions, tasks, genvars, typedefs, enum constants, instances,
     declarations in generate blocks included), nor one declared in a package or at
     compilation-unit scope of the same text; the finding names the collision;
   * the condition `i <op> E` or `E <op> i`, `<op>` one of `<` `<=` `>` `>=` `!=` `==`;
   * E (and the initial value, by the same grammar without the iterator) built by `+`, `-`,
     `*`, unary `-`/`+` and parentheses from unsized decimal literals (`4`, at most 2^31 - 1),
     the iterator, and parameters/localparams the SAME module declares (in its header or its
     body, and nowhere else in it) as `int` or `integer`, or untyped with an unsized decimal
     default; an untyped one only while no `defparam` and no instantiation of the module
     overrides a parameter with anything but an unsized decimal literal (an untyped parameter
     takes the type of the value it is given). Refused: sized or based literals (`2'd2`,
     `'d2`), unsigned or packed-typed parameters, ports, variables, other loops' iterators,
     calls, selects and every other operator;
   * ONE step: `i++`, `++i`, `i--`, `--i`, `i += n`, `i -= n`, `i = i + n`, `i = i - n` on the
     iterator itself, `n` a nonzero unsized decimal literal (refused: a step on a select
     `i[0]++`, a non-constant amount `i += d`, `i = i + i`, `i *= 2`, a second step).

What the gate does NOT cover: two tools that read the same text but give a
construct different semantics in some other way (a Yosys or ls-sv bug, a
synthesis don't-care not listed here). Those are ls-sv/Yosys
disagreements, bug reports, and the checker's post-synthesis check
(`check/postsynth.py`) rejects the submission where its vectors find them.

What the gate does not do either: re-lay-out the text. Scores do not depend
on layout because the scoring flow canonicalizes on the Yosys side
(`score/canon.ys`: a name-free RTLIL read by a fresh Yosys process), so the
gate keeps the submitted text's lines and columns and every finding points at
the ORIGINAL `file:line:col`.

Usage:
  python3.12 score/srcgate.py FILE.sv [--write OUT.sv] [--clock CLK]
Prints JSON {passed, findings, canonical_sha256}; exit status 0 = passes,
1 = rejected.
"""

import argparse
import hashlib
import json
import os
import re
import sys

# The qualifiers Yosys reads as `full_case` / `parallel_case` (see above).
SYNTH_QUALIFIERS = {"UniqueKeyword": "unique", "Unique0Keyword": "unique0",
                    "PriorityKeyword": "priority"}
# Directives both tools read the same way, and their admitted arguments.
ALLOWED_DIRECTIVES = {"TimeScaleDirective", "DefaultNetTypeDirective"}
DEFAULT_NETTYPES = {"none", "wire"}
# Host access (item 5 of the docstring). ONE ROW PER FAMILY: (family, what it
# does, the LRM clause, the system names). Matching is case-insensitive on the
# whole name (`HOST_SYSTEM_NAMES`) or on a prefix (`HOST_SYSTEM_PREFIXES`).
# Adding a name here is the whole change: the unit test (`test_srcgate.py`)
# generates one design per row of this table.
HOST_FAMILIES = (
    ("memfile", "reads or writes a memory array from or to a host file", "LRM 21.4, 21.5",
     "$readmemb $readmemh $writememb $writememh"),
    ("fileio", "opens, reads, writes or repositions a host file", "LRM 21.3",
     "$fopen $fclose $fgetc $ungetc $fgets $fscanf $fread $ftell $fseek $rewind $fflush $feof "
     "$ferror $fdisplay $fdisplayb $fdisplayh $fdisplayo $fwrite $fwriteb $fwriteh $fwriteo "
     "$fstrobe $fstrobeb $fstrobeh $fstrobeo $fmonitor $fmonitorb $fmonitorh $fmonitoro"),
    ("process", "runs a host program or reads the host environment or command line",
     "LRM 21.6 and tool extensions",
     "$system $shell $exec $test$plusargs $value$plusargs $getenv"),
    ("dump", "writes a waveform or dump file", "LRM 21.7 and vendor extensions",
     "$dumpfile $dumpvars $dumpon $dumpoff $dumpall $dumplimit $dumpflush $dumpports "
     "$dumpportson $dumpportsoff $dumpportsall $dumpportslimit $dumpportsflush "
     "$recordfile $recordvars"),
    ("coverage", "saves or merges a host coverage database", "LRM 40",
     "$coverage_save $coverage_merge $set_coverage_db_name $load_coverage_db"),
    ("sdf", "reads a host SDF file", "SDF annotation",
     "$sdf_annotate"),
    ("annex-d", "reads or writes a host command, log, key or checkpoint file",
     "LRM Annex D (optional tasks)",
     "$input $log $nolog $key $nokey $save $restart $incsave"),
)
# Vendor families, by prefix (their names are not in the LRM): FSDB (`$fsdbDumpfile`),
# Cadence SHM (`$shm_open`), VCS (`$vcdplusfile`), ModelSim WLF (`$wlfdump`).
HOST_PREFIXES = (
    ("dump", "$fsdb"), ("dump", "$shm_"), ("dump", "$vcdplus"), ("dump", "$wlf"),
)
HOST_SYSTEM_NAMES = {n.lower(): (fam, what, lrm)
                     for fam, what, lrm, names in HOST_FAMILIES for n in names.split()}
HOST_SYSTEM_PREFIXES = {pre.lower(): next((fam, what, lrm) for fam, what, lrm, _ in HOST_FAMILIES
                                          if fam == f) for f, pre in HOST_PREFIXES}
DPI_KINDS = {"DPIImport": "import", "DPIExport": "export"}
HOST_WHY = ("refused: a submission may not read or write host files, run programs, read the "
            "environment or call native code (P-NO-HOST-ACCESS)")


def host_family(name):
    """(family, what, lrm) when the system name `name` (with its `$`) reaches the
    host, else None."""
    low = name.lower()
    if low in HOST_SYSTEM_NAMES:
        return HOST_SYSTEM_NAMES[low]
    for pre, row in HOST_SYSTEM_PREFIXES.items():
        if low.startswith(pre):
            return row
    return None


# A comment Yosys would read as a pragma: `synopsys`/`synthesis`/`pragma` as
# its first word (Yosys's lexer rule), or one of the pragma words anywhere.
PRAGMA_COMMENT = re.compile(
    r"^(//|/\*)\s*(synopsys|synthesis|pragma)\b"
    r"|translate_off|translate_on|full_case|parallel_case", re.IGNORECASE)
# Literal digits that are not 0/1 (x, z and `?`, which is z), and the ones
# that are wildcards in a casez / casex item (the gate's item 4).
XZ_DIGITS = "xXzZ?"
WILDCARD_DIGITS = {"CaseZKeyword": "zZ?", "CaseXKeyword": "xXzZ?"}
ALLOWED_DIRECTIVE_TEXT = re.compile(
    r"`timescale\s+\d+\s*(s|ms|us|ns|ps|fs)\s*/\s*\d+\s*(s|ms|us|ns|ps|fs)\b"
    r"|`default_nettype\s+(none|wire)\b")


class GateError(Exception):
    pass


def _linecol(text, offset):
    line = text.count("\n", 0, offset) + 1
    col = offset - (text.rfind("\n", 0, offset) + 1) + 1
    return line, col


def _blank(s):
    """`s` with every non-whitespace character replaced by a space."""
    return "".join(c if c in " \t\r\n" else " " for c in s)


def strip_comments(text):
    """(canonical text, comments) where comments = [(offset, text)].

    A small SystemVerilog lexer that knows exactly what can hide a comment
    opener: string literals ("...", with backslash escapes) and escaped
    identifiers (backslash up to the next whitespace). Its result is
    VALIDATED by slang (`gate_text`), so a lexing mistake rejects rather
    than passing silently."""
    out, comments = [], []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            comments.append((i, text[i:j]))
            out.append(_blank(text[i:j]))
            i = j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            if j < 0:
                raise GateError("%d:%d: unterminated block comment" % _linecol(text, i))
            j += 2
            comments.append((i, text[i:j]))
            out.append(_blank(text[i:j]))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"' and text[j] != "\n":
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(text[i:j])
            i = j
        elif text[i] == "\\":
            j = i + 1
            while j < n and not text[j].isspace():
                j += 1
            out.append(text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out), comments


def _slang_scan(text, name):
    """slang's view of `text`: token sequence, comments, directives,
    attributes, case qualifiers, and skipped/disabled text."""
    import pyslang
    from pyslang import parsing, syntax
    tree = syntax.SyntaxTree.fromText(text, name)
    sm = tree.sourceManager
    TK, TV, SK = parsing.TokenKind, parsing.TriviaKind, syntax.SyntaxKind
    res = {"tokens": [], "comments": 0, "directives": [], "attributes": [],
           "qualifiers": [], "skipped": [], "xz_literals": [], "wildcards": [],
           "system_names": [], "escaped_dollar": [], "dpi": []}

    def where(loc):
        try:
            if sm.isMacroLoc(loc):      # a token a macro produced: point at the macro's use
                loc = sm.getFullyOriginalLoc(loc)
            return "%d:%d" % (sm.getLineNumber(loc), sm.getColumnNumber(loc))
        except Exception:
            return "?"

    def cb(node):
        if isinstance(node, parsing.Token):
            for tv in node.trivia:
                k = tv.kind
                if k in (TV.LineComment, TV.BlockComment):
                    res["comments"] += 1
                elif k == TV.Directive:
                    s = tv.syntax()
                    kind = str(s.kind).split(".")[-1]
                    res["directives"].append((kind, str(s).strip(), where(s.sourceRange.start)))
                elif k in (TV.DisabledText, TV.SkippedTokens, TV.SkippedSyntax):
                    res["skipped"].append((str(k).split(".")[-1], where(node.location)))
            kind = str(node.kind).split(".")[-1]
            if kind in SYNTH_QUALIFIERS:
                res["qualifiers"].append((SYNTH_QUALIFIERS[kind], where(node.location)))
            if node.kind == TK.SystemIdentifier:
                res["system_names"].append((node.valueText or node.rawText, where(node.location)))
            elif node.kind == TK.Identifier and node.valueText.startswith("$"):
                res["escaped_dollar"].append((node.rawText, where(node.location)))
            if node.kind != TK.EndOfFile:
                res["tokens"].append((kind, node.rawText))
        elif node.kind in (SK.DPIImport, SK.DPIExport):
            res["dpi"].append((DPI_KINDS[str(node.kind).split(".")[-1]],
                               " ".join(str(node).split())[:50], where(node.sourceRange.start)))
        elif node.kind == SK.AttributeInstance:
            res["attributes"].append((str(node).strip(), where(node.sourceRange.start)))
        elif node.kind in (SK.IntegerVectorExpression, SK.UnbasedUnsizedLiteralExpression):
            tok = node.value if node.kind == SK.IntegerVectorExpression else node.literal
            digits = tok.rawText if node.kind == SK.IntegerVectorExpression else \
                tok.rawText[1:]
            if any(c in XZ_DIGITS for c in digits):
                r = node.sourceRange
                res["xz_literals"].append((r.start.offset, set(digits) & set(XZ_DIGITS),
                                           str(node).strip(), where(r.start)))
        elif node.kind == SK.CaseStatement:
            allowed = WILDCARD_DIGITS.get(str(node.caseKeyword.kind).split(".")[-1])
            mi = node.matchesOrInside      # an absent token is kind Unknown, not None
            if allowed and (mi is None or mi.kind == TK.Unknown):
                for item in node.items:
                    if item.kind != SK.StandardCaseItem:
                        continue
                    for e in item.expressions:
                        if isinstance(e, parsing.Token):
                            continue     # the separating commas
                        r = e.sourceRange
                        res["wildcards"].append((r.start.offset, r.end.offset, allowed))
        return pyslang.ast.VisitAction.Advance

    tree.root.visit(cb)
    return res


# The clocked rules (item 6 of the docstring), by slang syntax kind.
TIMING_DELAYS = {"DelayControl", "CycleDelay"}
TIMING_EVENTS = {"EventControl", "EventControlWithExpression", "ImplicitEventControl",
                 "RepeatedEventControl"}
CLOCKED_REFUSED = {
    "InitialBlock": "`initial` block (state before the first reset is the checker's random state; "
                    "C1: claims start after a reset)",
    "FinalBlock": "`final` block (simulation only)",
    "AlwaysLatchBlock": "`always_latch` (a level-sensitive latch: the clocked profile has flops only)",
    "WaitStatement": "`wait` (a timing control: one clock edge per cycle is the protocol)",
    "WaitForkStatement": "`wait fork` (a timing control)",
    "WaitOrderStatement": "`wait_order` (a timing control)",
    "ParallelBlockStatement": "`fork` block (concurrent processes inside a procedure)",
    "DisableForkStatement": "`disable fork`",
}
# (slang's prefix forms are `Unary...`: `++c` is a `UnaryPreincrementExpression`.)
BLOCKING_KINDS = {"PostincrementExpression", "UnaryPreincrementExpression",
                  "PostdecrementExpression", "UnaryPredecrementExpression"}
ONLY_NBA = ("only `<=`: every register updates from the pre-edge state; the one blocking write "
            "admitted is a `for` loop's header step on the iterator its own header declares, "
            "`for (int i = 0; i < N; i++)`")
NO_TEMPS = ("the clock-step profile, `Stmt2.nbaOnly`, does not admit block-local temporaries "
            "yet")


def clocked_findings(text, name, clock):
    """(message, loc) per construct a CLOCKED task refuses (item 6): every edge process is
    `always_ff @(posedge <clock>)` exactly (one clock, one edge, no second event, so no
    asynchronous reset, no `iff`), with no blocking assignment in its body but the header step
    of a `for` loop on the iterator that header declares, and no other write to that iterator;
    no `initial`, `final` or `always_latch`; no delay, `wait`, `fork` or any other event control;
    no initializer on a variable's declaration (or a variable port's)."""
    import pyslang
    from pyslang import parsing, syntax
    tree = syntax.SyntaxTree.fromText(text, name)
    sm = tree.sourceManager
    out = []

    def kind(n):
        return str(n.kind).split(".")[-1]

    def at(n, msg):
        loc = n.location if isinstance(n, parsing.Token) else n.sourceRange.start
        out.append((msg, "%d:%d" % (sm.getLineNumber(loc), sm.getColumnNumber(loc))))

    def inside(n, k):
        p = n.parent
        while p is not None and kind(p) != k:
            p = p.parent
        return p is not None

    def header(blk):
        """The finding for an `always_ff` whose timing control is not `@(posedge <clock>)`."""
        st = blk.statement
        tc = st.timingControl if kind(st) == "TimingControlStatement" else None
        e = tc.expr if tc is not None and kind(tc) == "EventControlWithExpression" else None
        while e is not None and kind(e) == "ParenthesizedEventExpression":
            e = e.expr
        if e is None or kind(e) not in ("SignalEventExpression", "BinaryEventExpression"):
            return blk, f"`always_ff` must start with `@(posedge {clock})`"
        if kind(e) == "BinaryEventExpression":
            return e, ("a second event in an `always_ff` sensitivity list (an asynchronous reset "
                       f"or a second clock): only `@(posedge {clock})`, the reset is synchronous (C1)")
        edge = e.edge.rawText if e.edge is not None else ""
        if edge != "posedge":
            return e, (f"`{edge or 'level-sensitive'}` event: one edge, `posedge {clock}`")
        if e.iffClause is not None:
            return e.iffClause, "`iff` on the clock event (a gated clock)"
        sig = str(e.expr).strip()
        if kind(e.expr) != "IdentifierName" or sig != clock:
            return e.expr, (f"clocked by `{sig}`: the task has exactly one clock, `{clock}`")
        return None

    def nodes(lst):
        return [x for x in lst if not isinstance(x, parsing.Token)]

    def unparen(e):
        while e is not None and kind(e) == "ParenthesizedExpression":
            e = e.expression
        return e

    def name_of(e):
        """The variable a target names: `x` or a select of it (`x[i]`, `x[i +: 8]`), else None."""
        e = unparen(e)
        if e is not None and kind(e) in ("IdentifierName", "IdentifierSelectName"):
            return e.identifier.valueText
        return None

    def target(n):
        return n.operand if kind(n) in BLOCKING_KINDS else n.left

    def header_names(loop):
        """The iterators a `for` header DECLARES (`for (int i = 0; ...)`: slang's
        ForVariableDeclaration), or None when an initializer assigns a variable declared
        elsewhere (`for (i = 0; ...)`)."""
        names = []
        for x in nodes(loop.initializers):
            if kind(x) != "ForVariableDeclaration":
                return None
            names.append(x.declarator.name.valueText)
        return names

    def resolve(n, name):
        """Where `name`, written at `n`, is declared INSIDE the enclosing `always_ff`: ("iterator",
        loop) for an enclosing `for` header, ("local", block) for a declaration of an enclosing
        block (innermost first), None when it is declared outside the process."""
        p = n.parent
        while p is not None and kind(p) != "AlwaysFFBlock":
            k = kind(p)
            if k == "ForLoopStatement" and name in (header_names(p) or []):
                return "iterator", p
            if k in ("SequentialBlockStatement", "ParallelBlockStatement"):
                for item in nodes(p.items):
                    if kind(item) == "DataDeclaration" and any(
                            d.name.valueText == name for d in nodes(item.declarators)):
                        return "local", p
            p = p.parent
        return None

    def iterator_write(name):
        return (f"write to the `for` loop iterator `{name}` outside its header step (in "
                "SystemVerilog a write in the body changes the iteration sequence, while the "
                "loop's expansion computes its values from the header alone)")

    def write_finding(n, name, where):
        """The finding for a blocking write to `name` resolved at `where` (see `resolve`)."""
        if where is not None and where[0] == "iterator":
            return iterator_write(name)
        if where is not None:
            return (f"blocking assignment in `always_ff` to the block-local variable `{name}` "
                    f"({NO_TEMPS}; {ONLY_NBA})")
        if name is None:
            return f"blocking assignment in `always_ff` ({ONLY_NBA})"
        return (f"blocking assignment in `always_ff` to `{name}`, declared outside the process "
                f"(another process can see it; {ONLY_NBA})")

    def in_loop_header(n):
        """`n` stands in the header of the `for` loop nearest above it (a header holds expressions
        only, so no other loop can sit between them)."""
        p = n.parent
        while p is not None and kind(p) not in ("ForLoopStatement", "AlwaysFFBlock"):
            p = p.parent
        return (p is not None and kind(p) == "ForLoopStatement"
                and n.sourceRange.start.offset < p.closeParen.location.offset)

    def blocking_finding(n):
        """The finding for a blocking write `n` inside an `always_ff`, or None (admitted)."""
        if in_loop_header(n):
            return None     # item 7 (`loop_findings`) judges every `for` header, in every process
        name = name_of(target(n))
        return write_finding(n, name, resolve(n, name) if name else None)

    def cb(n):
        if isinstance(n, parsing.Token):
            return pyslang.ast.VisitAction.Advance
        k = kind(n)
        if k in CLOCKED_REFUSED:
            at(n, CLOCKED_REFUSED[k])
        elif k == "AlwaysFFBlock":
            bad = header(n)
            if bad:
                at(*bad)
        elif k in TIMING_DELAYS:
            at(n, "delay (a timing control: one clock edge per cycle is the protocol)")
        elif k in TIMING_EVENTS:
            p = n.parent
            if not (p is not None and kind(p) == "TimingControlStatement"
                    and p.parent is not None and kind(p.parent) == "AlwaysFFBlock"):
                at(n, "event control outside an `always_ff` header (an extra timing control; "
                      "use `always_ff @(posedge clk)` or `always_comb`)")
        elif k == "SignalEventExpression" and n.edge is not None \
                and n.edge.rawText in ("negedge", "edge"):
            at(n, f"`{n.edge.rawText}`: one edge, the clock's `posedge`")
        elif k == "NonblockingAssignmentExpression" and inside(n, "AlwaysFFBlock"):
            name = name_of(n.left)
            where = resolve(n, name) if name else None
            if where is not None and where[0] == "iterator":
                at(n, iterator_write(name))
        elif (k in BLOCKING_KINDS or k.endswith("AssignmentExpression")) \
                and inside(n, "AlwaysFFBlock"):
            msg = blocking_finding(n)
            if msg:
                at(n, msg)
        elif k == "Declarator" and n.initializer is not None and n.parent is not None:
            pk = kind(n.parent)
            const = pk == "DataDeclaration" and any(t.rawText == "const" for t in n.parent.modifiers)
            if pk in ("DataDeclaration", "ImplicitAnsiPort", "PortDeclaration") and not const:
                at(n, f"initializer on the declaration of `{n.name.rawText}` (a time-zero value: "
                      "state comes from the reset, C1)")
        return pyslang.ast.VisitAction.Advance

    tree.root.visit(cb)
    return out


# The procedural `for` loop stopgap (item 7 of the docstring), by slang syntax kind.
LOOP_ITER_TYPES = {"IntType", "IntegerType"}              # `int`, `integer`
LOOP_COMPARE = {"LessThanExpression", "LessThanEqualExpression", "GreaterThanExpression",
                "GreaterThanEqualExpression", "InequalityExpression", "EqualityExpression"}
LOOP_ARITH = {"AddExpression", "SubtractExpression", "MultiplyExpression"}
LOOP_UNARY = {"UnaryMinusExpression", "UnaryPlusExpression"}
# The steps admitted on the header's iterator `i`: `i++`, `++i`, `i--`, `--i`, `i += k`, `i -= k`,
# `i = i + k`, `i = i - k` (k an unsized decimal literal, not 0): the forms the extractor keeps as
# a `For` (extract.py `_sym_for_step_node`, `_sym_for_delta`).
LOOP_STEP_UNARY = BLOCKING_KINDS
LOOP_STEP_COMPOUND = {"AddAssignmentExpression", "SubtractAssignmentExpression"}
LOOP_STEP_LINEAR = {"AddExpression", "SubtractExpression"}
# The scopes whose names an iterator may not reuse, and the kinds a module-scope walk does not
# enter (their declarations are not module-scope names).
LOOP_UNITS = {"ModuleDeclaration", "InterfaceDeclaration", "ProgramDeclaration",
              "PackageDeclaration"}
LOOP_INNER_SCOPES = {"FunctionDeclaration", "TaskDeclaration", "AlwaysBlock", "AlwaysCombBlock",
                     "AlwaysFFBlock", "AlwaysLatchBlock", "InitialBlock", "FinalBlock",
                     "ClassDeclaration", "StructType", "UnionType"} | LOOP_UNITS
LOOP_GENERATE_SCOPES = {"GenerateBlock", "LoopGenerate", "IfGenerate", "CaseGenerate"}
INT_MAX = 2 ** 31 - 1
# The three measured ls-sv defects (and the expansion they live in) that item 7 stands in for.
LOOP_DEFECTS = {
    "cond": "ls-sv evaluates a `for` header's comparison and arithmetic as signed integers where "
            "SystemVerilog computes unsigned (a sized literal, an unsigned or packed operand)",
    "name": "ls-sv binds a `for` iterator by name in the module's parameter table, so an iterator "
            "spelled like a module-scope name captures that name (inside an inlined function, "
            "for one)",
    "type": "ls-sv ignores a `for` iterator's declared type (a `bit [2:0]` iterator wraps in "
            "SystemVerilog, not in ls-sv)",
    "shape": "ls-sv expands a `for` loop from its header alone, one body copy per iterator value",
}
LOOP_ADMITTED = ("admitted: `for (int i = E; i < E; i++)` with `<`/`<=`/`>`/`>=`/`!=`/`==`, the "
                 "steps `i++` `i--` `i += k` `i -= k` `i = i + k` `i = i - k`, E built by + - * "
                 "from unsized decimal literals, the iterator and this module's `int`/`integer` "
                 "or untyped decimal parameters")


def _kind(n):
    return str(n.kind).split(".")[-1]


def _present(tok):
    """A token slang did not synthesize as missing (an absent token has empty text)."""
    return tok is not None and tok.rawText != ""


def _walk(top, stop=frozenset()):
    """Every syntax node at or below `top` (slang's own traversal), not entering a node whose kind
    NAME is in `stop` (but listing it); `top` itself is always entered."""
    import pyslang
    from pyslang import parsing, syntax
    stop = {getattr(syntax.SyntaxKind, k) for k in stop if hasattr(syntax.SyntaxKind, k)}
    out = []
    adv, skip = pyslang.ast.VisitAction.Advance, pyslang.ast.VisitAction.Skip

    def cb(n):
        if isinstance(n, parsing.Token):
            return adv
        out.append(n)
        return skip if len(out) > 1 and n.kind in stop else adv
    top.visit(cb)
    return out


_DECLARATOR_WHAT = {"ParameterDeclaration": "parameter", "DataDeclaration": "variable",
                    "NetDeclaration": "net", "ImplicitAnsiPort": "port", "PortDeclaration": "port",
                    "EnumType": "enum constant", "FunctionPort": "function argument",
                    "ForVariableDeclaration": "`for` iterator"}


def _declared(x):
    """[(name, what, name token)] that the syntax node `x` itself declares."""
    from pyslang import parsing
    k = _kind(x)
    if k == "Declarator":
        p = x.parent
        what = _DECLARATOR_WHAT.get(_kind(p), "declaration") if p is not None else "declaration"
        if what == "parameter" and _present(p.keyword):
            what = p.keyword.rawText
        return [(x.name.valueText, what, x.name)] if _present(x.name) else []
    if k in ("FunctionDeclaration", "TaskDeclaration"):
        nm = x.prototype.name
        tok = nm.identifier if _kind(nm) == "IdentifierName" else nm.getFirstToken()
        return [(tok.valueText, "function" if k == "FunctionDeclaration" else "task", tok)]
    if k == "GenvarDeclaration":
        return [(i.identifier.valueText, "genvar", i.identifier) for i in x.identifiers
                if not isinstance(i, parsing.Token)]
    tok = {"TypeAssignment": "name", "TypedefDeclaration": "name",
           "ForwardTypedefDeclaration": "name", "InstanceName": "name", "ExplicitAnsiPort": "name",
           "ClassDeclaration": "name", "LoopGenerate": "identifier"}.get(k)
    if tok is None or not _present(getattr(x, tok)):
        return []
    what = {"TypeAssignment": "type parameter", "TypedefDeclaration": "typedef",
            "ForwardTypedefDeclaration": "typedef", "InstanceName": "instance",
            "ExplicitAnsiPort": "port", "ClassDeclaration": "class", "LoopGenerate": "genvar"}[k]
    return [(getattr(x, tok).valueText, what, getattr(x, tok))]


def _unsized_decimal(e):
    """`e` is an unsized decimal literal (`4`, `1_000`) that fits a 32-bit `int`."""
    if e is None or _kind(e) != "IntegerLiteralExpression":
        return False
    digits = e.literal.rawText.replace("_", "")
    return digits.isdigit() and int(digits) <= INT_MAX


def loop_findings(text, name):
    """(message, loc) per procedural `for` loop header that item 7 does not admit, in every
    process kind and in functions and tasks: the iterator declared in the header as `int` or
    `integer` (one iterator, with an initial value) and named like nothing declared at module
    scope; the condition `i <op> E` or `E <op> i`; the step `i++`/`++i`/`i--`/`--i`/`i += k`/
    `i -= k`/`i = i + k`/`i = i - k`; E (and the initial value, the same grammar without the
    iterator) built by `+ - *` (and unary `-`, parentheses) from unsized decimal literals, the
    iterator and parameters the enclosing module declares as `int`/`integer` or untyped with an
    unsized decimal default."""
    import pyslang
    from pyslang import parsing, syntax
    tree = syntax.SyntaxTree.fromText(text, name)
    sm = tree.sourceManager
    out = []
    kind = _kind

    def loc_of(n):
        loc = n.location if isinstance(n, parsing.Token) else n.sourceRange.start
        return "%d:%d" % (sm.getLineNumber(loc), sm.getColumnNumber(loc))

    def at(n, reason, defect):
        out.append((f"procedural `for` loop: {reason} (svGolf stopgap until ls-sv fixes its `for` "
                    f"loops: {LOOP_DEFECTS[defect]}; {LOOP_ADMITTED})", loc_of(n)))

    def nodes(lst):
        return [x for x in lst if x is not None and not isinstance(x, parsing.Token)]

    def unparen(e):
        while e is not None and kind(e) == "ParenthesizedExpression":
            e = e.expression
        return e

    def text_of(n):
        return " ".join(str(n).split())[:60]

    SK = syntax.SyntaxKind
    loops, insts, defparams = [], [], []
    found = {SK.ForLoopStatement: loops, SK.HierarchyInstantiation: insts, SK.DefParam: defparams}

    def collect(n):
        lst = None if isinstance(n, parsing.Token) else found.get(n.kind)
        if lst is not None:
            lst.append(n)
        return pyslang.ast.VisitAction.Advance
    tree.root.visit(collect)
    if not loops:
        return out
    # What every unit (module, interface, program, package) declares, computed once per unit.
    units = {}

    def unit_of(n):
        p = n.parent
        while p is not None and kind(p) not in LOOP_UNITS:
            p = p.parent
        return p if p is not None else tree.root

    # The compilation unit's own names and every package's: visible in a module by `$unit` or an
    # import, so an iterator may not reuse them either.
    outer = {}
    for x in _walk(tree.root, LOOP_INNER_SCOPES - {"PackageDeclaration"}):
        for nm, what, tok in _declared(x):
            outer.setdefault(nm, (what, tok))
    # A module whose untyped parameters a `defparam` or an instantiation may override with a sized
    # or computed value (an untyped parameter takes the type of the value it is given).
    has_defparam = bool(defparams)
    retyped = set()
    for x in insts:
        if x.parameters is not None:
            for a in nodes(x.parameters.parameters):
                if not _unsized_decimal(unparen(getattr(a, "expr", None))):
                    retyped.add(x.type.valueText)

    def unit_info(u):
        key = (str(u.kind), u.sourceRange.start.offset)     # wrappers are not stable objects
        if key in units:
            return units[key]
        scope = {}                      # name -> (what, token): module-scope names (item 7's set)
        for x in _walk(u, LOOP_INNER_SCOPES)[1:]:          # [0] is `u` itself
            for nm, what, tok in _declared(x):
                scope.setdefault(nm, (what, tok))
        count = {}                      # name -> declarations anywhere in the unit
        for x in _walk(u):
            for nm, _, _ in _declared(x):
                count[nm] = count.get(nm, 0) + 1
        params = {}                     # name -> (ParameterDeclaration, Declarator), unit level
        for x in _walk(u, LOOP_INNER_SCOPES | LOOP_GENERATE_SCOPES):
            if kind(x) == "ParameterDeclaration":
                for d in nodes(x.declarators):
                    params[d.name.valueText] = (x, d)
        uname = u.header.name.valueText if kind(u) in LOOP_UNITS else None
        units[key] = (scope, count, params, uname)
        return units[key]

    def param_problem(nm, u):
        """None when `nm` names a parameter of unit `u` that item 7 admits in E, else why not."""
        scope, count, params, uname = unit_info(u)
        if nm not in params:
            return (f"`{nm}` is not a parameter or localparam that this module declares (E may "
                    "name only the iterator and this module's `int`/`integer` or untyped decimal "
                    "parameters)")
        decl, d = params[nm]
        if count.get(nm, 0) != 1:
            return f"the parameter `{nm}` is declared again in a nested scope (which one E reads)"
        t = decl.type
        tk = kind(t) if t is not None else "ImplicitType"
        signing = t.signing.rawText if t is not None and _present(getattr(t, "signing", None)) \
            else ""
        dims = nodes(getattr(t, "dimensions", None) or []) if t is not None else []
        if tk in LOOP_ITER_TYPES and signing in ("", "signed") and not dims:
            return None
        if tk == "ImplicitType" and not signing and not dims:
            init = d.initializer.expr if d.initializer is not None else None
            if not _unsized_decimal(unparen(init)):
                return (f"the untyped parameter `{nm}` has the default `{text_of(init)}`, not an "
                        "unsized decimal literal (an untyped parameter takes its value's type)")
            if has_defparam or uname in retyped:
                return (f"the untyped parameter `{nm}` may be given a sized or computed value "
                        "(a `defparam`, or an instantiation of this module that overrides a "
                        "parameter with something other than an unsized decimal literal), and an "
                        "untyped parameter takes its value's type; declare it `int`")
            return None
        return (f"the parameter `{nm}` is declared `{text_of(t) or 'untyped'}` (E may name only "
                "parameters declared `int` or `integer`, or untyped with an unsized decimal "
                "default)")

    def bad_expr(e, it, u):
        """(node, why) for the first part of E that item 7 does not admit, else None. `it` is the
        iterator E may name (None: the initial value, which may not)."""
        stack = [e]
        while stack:
            x = unparen(stack.pop())
            k = kind(x)
            if k in LOOP_ARITH:
                stack += [x.right, x.left]
            elif k in LOOP_UNARY:
                stack.append(x.operand)
            elif k == "IntegerLiteralExpression":
                if not _unsized_decimal(x):
                    return x, f"the literal `{text_of(x)}` does not fit a 32-bit `int`"
            elif k in ("IntegerVectorExpression", "UnbasedUnsizedLiteralExpression"):
                return x, (f"the literal `{text_of(x)}` is sized or based (unsigned, unless `'s`; "
                           "only unsized decimal literals such as `4`)")
            elif k == "IdentifierName":
                nm = x.identifier.valueText
                if it is not None and nm == it:
                    continue
                why = param_problem(nm, u)
                if why:
                    return x, why
            else:
                return x, (f"`{text_of(x)}` (only + - * over unsized decimal literals, the "
                           "iterator and this module's `int`/`integer` or untyped decimal "
                           "parameters)")
        return None

    def is_iter(e, it):
        e = unparen(e)
        return e is not None and kind(e) == "IdentifierName" and e.identifier.valueText == it

    def check(loop):
        u = unit_of(loop)
        inits = nodes(loop.initializers)
        if not inits:
            return at(loop, "the header declares no iterator", "shape")
        if kind(inits[0]) != "ForVariableDeclaration":
            first = inits[0]
            nm = text_of(first.left) if kind(first) == "AssignmentExpression" else text_of(first)
            return at(first, f"the iterator `{nm}` is not declared in the loop header "
                             f"(`{text_of(first)}` assigns a variable declared elsewhere: the "
                             "expansion never writes it, and its declared type is not read); "
                             f"declare it, `for (int {nm} = ...; ...)`", "shape")
        if len(inits) > 1:
            return at(inits[1], "the header declares more than one iterator (one per loop)",
                      "shape")
        decl = inits[0]
        dl = decl.declarator
        it = dl.name.valueText
        t = decl.type
        signing = t.signing.rawText if t is not None and _present(getattr(t, "signing", None)) \
            else ""
        if t is None or kind(t) not in LOOP_ITER_TYPES or signing not in ("", "signed") \
                or nodes(getattr(t, "dimensions", None) or []) or nodes(dl.dimensions):
            at(t if t is not None and str(t).strip() else decl,
               f"{f'the iterator `{it}`' if it else 'the header'} is declared "
               f"`{text_of(decl).split('=')[0].strip()}` (only "
               "`int` or `integer`)", "type")
        if not it:
            return None                 # `for (var i = 0; ...)`: slang reads `i` as a type name
        scope = unit_info(u)[0]
        clash = scope.get(it) or outer.get(it)
        if clash:
            what, tok = clash
            at(dl.name, f"the iterator `{it}` has the name of the {what} `{it}` declared at "
                        f"{loc_of(tok)}", "name")
        init = dl.initializer.expr if dl.initializer is not None else None
        if init is None:
            at(dl, f"the iterator `{it}` has no initial value", "shape")
        else:
            bad = bad_expr(init, None, u)
            if bad:
                at(bad[0], f"the initial value: {bad[1]}", "cond")
        cond = unparen(loop.stopExpr)
        if cond is None:
            at(loop, "the header has no condition", "shape")
        elif kind(cond) not in LOOP_COMPARE \
                or not (is_iter(cond.left, it) or is_iter(cond.right, it)):
            at(cond, f"the condition `{text_of(cond)}` is not `{it} <op> E` or `E <op> {it}` with "
                     "<op> one of `<` `<=` `>` `>=` `!=` `==`", "cond")
        else:
            bad = bad_expr(cond.right if is_iter(cond.left, it) else cond.left, it, u)
            if bad:
                at(bad[0], f"the condition: {bad[1]}", "cond")
        steps = nodes(loop.steps)
        if not steps:
            at(loop, "the header has no step", "shape")
        for s in steps[1:]:
            at(s, f"a second step `{text_of(s)}` (one step per loop)", "shape")
        if steps and not step_ok(steps[0], it):
            at(steps[0], f"the step `{text_of(steps[0])}` (only `{it}++`, `{it}--`, `{it} += <n>`, "
                         f"`{it} -= <n>`, `{it} = {it} + <n>`, `{it} = {it} - <n>` on the "
                         "iterator itself, with <n> a nonzero unsized decimal literal)", "shape")

    def step_ok(s, it):
        k = kind(s)
        if k in LOOP_STEP_UNARY:
            return is_iter(s.operand, it)
        if k in LOOP_STEP_COMPOUND:
            k_ = unparen(s.right)
        elif k == "AssignmentExpression":
            r = unparen(s.right)
            if r is None or kind(r) not in LOOP_STEP_LINEAR or not is_iter(r.left, it):
                return False
            k_ = unparen(r.right)
        else:
            return False
        return (is_iter(s.left, it) and kind(unparen(s.left)) == "IdentifierName"
                and _unsized_decimal(k_) and int(k_.literal.rawText.replace("_", "")) > 0)

    for x in loops:
        check(x)
    return out


def xz_literal_findings(scan):
    """(message, loc) per literal with an x/z/? digit that is not a wildcard
    of the casez/casex item it stands in."""
    out = []
    for off, digits, text, loc in scan["xz_literals"]:
        ok = [allowed for lo, hi, allowed in scan["wildcards"] if lo <= off < hi]
        if ok and digits <= set(ok[-1]):
            continue
        if ok:
            why = (f"literal {text[:40]!r}: only {' '.join(sorted(ok[-1]))} are wildcards in "
                   "this case item")
        else:
            why = f"x/z literal {text[:40]!r}"
        out.append((why + " (an x or z bit is a don't-care that Yosys resolves freely and "
                    "drops from comparisons, and an unknown value to ls-sv: the proved and the "
                    "scored circuits would differ; only casez/casex item wildcards are "
                    "accepted)", loc))
    return out


def gate_text(text, name="design.sv", clock=None):
    """(canonical text or None, findings). Findings are `name:line:col: msg`. With `clock`
    (a clocked task's clock port), the clocked rules (item 6) apply too."""
    found = {}   # "name:line:col" -> message (the first finding at a location)

    def at(offset, msg):
        line, col = _linecol(text, offset)
        found.setdefault(f"{name}:{line}:{col}", msg)

    def at_loc(loc, msg):
        found.setdefault(f"{name}:{loc}", msg)

    try:
        canon, comments = strip_comments(text)
    except GateError as e:
        return None, [f"{name}:{e}"]
    for off, c in comments:
        if PRAGMA_COMMENT.search(c):
            at(off, "synthesis-pragma comment (Yosys would read it, slang would not): "
               f"{c[:60]!r}")
    # characters: printable ASCII, tab, CR, LF outside comments
    for m in re.finditer(r"[^\x20-\x7e\t\r\n]", canon):
        at(m.start(), f"character {m.group()!r} outside a comment (only printable ASCII)")
        break
    # what Yosys's lexer could read as a comment, attribute or directive
    for pat, msg in ((r"//|/\*", "`//` or `/*` outside a comment (inside a string or an "
                      "escaped identifier)"),
                     (r"\(\*(?!\s*\))", "attribute `(* ... *)` (Yosys gives attributes a "
                      "synthesis meaning, slang none)"),
                     (r"\{\*|\*\}", "`{*` / `*}` (Yosys default attributes)")):
        for m in re.finditer(pat, canon):
            at(m.start(), msg)
    for m in re.finditer(r"`", canon):
        if not ALLOWED_DIRECTIVE_TEXT.match(canon, m.start()):
            word = re.match(r"`\w*", canon[m.start():]).group()
            at(m.start(), f"compiler directive or macro {word} (only `timescale and "
               "`default_nettype none|wire are accepted; Yosys predefines SYNTHESIS and "
               "YOSYS, slang does not)")
    # slang's view of the submitted text and of the canonical text
    orig = _slang_scan(text, name)
    for kind, body, loc in orig["directives"]:
        ok = kind in ALLOWED_DIRECTIVES
        if kind == "DefaultNetTypeDirective":
            parts = body.split()
            ok = len(parts) >= 2 and parts[1] in DEFAULT_NETTYPES
        if not ok:
            at_loc(loc, f"compiler directive ({kind}): {body[:60]!r}")
    for kind, loc in orig["skipped"]:
        at_loc(loc, f"preprocessor-skipped text ({kind})")
    for body, loc in orig["attributes"]:
        at_loc(loc, f"attribute {body[:60]!r} (Yosys gives attributes a synthesis meaning, "
               "slang none)")
    for msg, loc in xz_literal_findings(orig):
        at_loc(loc, msg)
    for sysname, loc in orig["system_names"]:
        row = host_family(sysname)
        if row:
            fam, what, lrm = row
            at_loc(loc, f"host access: `{sysname}` {what} ({lrm}); {HOST_WHY}")
    for raw, loc in orig["escaped_dollar"]:
        at_loc(loc, f"escaped identifier {raw!r} that begins with `$`: Yosys's lexer gives it the "
               "name of the system task of that spelling (and runs it, `$readmemh` included), "
               "slang reads an ordinary identifier, so the two tools read different programs "
               "(P-NO-HOST-ACCESS, P-SAME-PROGRAM)")
    for kind, text, loc in orig["dpi"]:
        at_loc(loc, f"host access: DPI {kind} {text!r} calls native code (LRM 35); {HOST_WHY}")
    for q, loc in orig["qualifiers"]:
        at_loc(loc, f"`{q}` qualifier (Yosys reads it as full_case/parallel_case, a "
               "synthesis don't-care; ls-sv runs the first matching arm)")
    for msg, loc in loop_findings(text, name):
        at_loc(loc, msg)
    if clock is not None:
        for msg, loc in clocked_findings(text, name, clock):
            at_loc(loc, f"clocked task: {msg}")
    if found:
        return None, sorted((f"{k}: {v}" for k, v in found.items()), key=_finding_key)
    can = _slang_scan(canon, name)
    if can["comments"]:
        return None, [f"{name}: internal: the canonical text still has {can['comments']} "
                      "comment(s) per slang"]
    if can["tokens"] != orig["tokens"]:
        k = next((i for i, (a, b) in enumerate(zip(can["tokens"], orig["tokens"])) if a != b),
                 min(len(can["tokens"]), len(orig["tokens"])))
        return None, [f"{name}: internal: stripping comments changed slang's token stream "
                      f"at token {k}; refusing the file"]
    return canon, []


def _finding_key(f):
    m = re.search(r":(\d+):(\d+):", f)
    return (int(m.group(1)), int(m.group(2)), f) if m else (0, 0, f)


def gate_file(path, name=None, clock=None):
    """(canonical text or None, findings) for the file at `path`."""
    with open(path, "rb") as fh:
        raw = fh.read()
    name = name or os.path.basename(path)
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as e:
        return None, [f"{name}: not UTF-8 ({e})"]
    return gate_text(text, name, clock)


def canonicalize(path, out_path, name=None):
    """Gate `path` and write its canonical text to `out_path`. Raises
    GateError with the findings when the gate rejects."""
    canon, findings = gate_file(path, name)
    if findings:
        raise GateError("\n".join(findings))
    with open(out_path, "w", newline="") as fh:
        fh.write(canon)
    return hashlib.sha256(canon.encode()).hexdigest()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("source")
    ap.add_argument("--write", help="write the canonical text here")
    ap.add_argument("--clock", help="a clocked task's clock port: apply the clocked rules (item 6)")
    args = ap.parse_args(argv)
    canon, findings = gate_file(args.source, clock=args.clock)
    res = {"passed": not findings, "findings": findings}
    if canon is not None:
        res["canonical_sha256"] = hashlib.sha256(canon.encode()).hexdigest()
        if args.write:
            with open(args.write, "w", newline="") as fh:
                fh.write(canon)
    print(json.dumps(res, indent=2, sort_keys=True))
    return 0 if not findings else 1


if __name__ == "__main__":
    sys.exit(main())
