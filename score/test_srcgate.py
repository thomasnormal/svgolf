#!/usr/bin/env python3.12
"""Tests for srcgate.py, the source gate in front of the extractor, the
banlist and Yosys.

    python3.12 score/test_srcgate.py
"""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import srcgate  # noqa: E402

GATE = os.path.join(HERE, "tests", "gate")

# fixture -> the substrings its findings must contain (empty: passes)
EXPECT = {
    "ok_comments.sv": [],
    "ifdef_synth.sv": ["`ifdef", "`else", "`endif"],
    "ifdef_yosys.sv": ["`ifdef"],
    "translate_off2.sv": ["synthesis-pragma comment"],
    "full_case.sv": ["synthesis-pragma comment"],
    "attr_full_case.sv": ["attribute"],
    "unique_case.sv": ["`unique` qualifier"],
    "priority_case.sv": ["`priority` qualifier"],
    "bad_hidden_comment.sv": ["inside a string or an escaped identifier",
                              "synthesis-pragma comment", "`default_nettype"],
    "xz_case_items.sv": ["5:37: x/z literal \"1'bz\"", "7:25: x/z literal \"2'b1z\"",
                         "9:9: x/z literal \"'x\"", "11:7: x/z literal \"2'b0z\"",
                         "12:7: x/z literal \"2'b1z\"", "13:14: x/z literal \"4'd?\""],
    "ok_casez_wildcards.sv": [],
    "casez_x_item.sv": ["6:7: literal \"4'b1x?0\": only ? Z z are wildcards"],
    # host access (P-NO-HOST-ACCESS)
    "host_readmemh.sv": ["12:11: host access: `$readmemh`"],
    "host_memfile_write.sv": ["10:5: host access: `$readmemb`", "11:5: host access: `$writememh`",
                              "12:5: host access: `$writememb`"],
    "host_fopen.sv": ["9:10: host access: `$fopen`", "10:5: host access: `$fdisplay`",
                      "11:5: host access: `$fwrite`", "12:5: host access: `$fstrobe`",
                      "13:5: host access: `$fmonitor`", "14:5: host access: `$fclose`"],
    "host_fread.sv": ["13:9: host access: `$fscanf`", "14:9: host access: `$fgets`",
                      "15:9: host access: `$fgetc`", "16:9: host access: `$fread`",
                      "17:9: host access: `$fseek`", "18:9: host access: `$ftell`",
                      "19:9: host access: `$feof`", "20:9: host access: `$ungetc`",
                      "21:9: host access: `$ferror`", "22:5: host access: `$rewind`",
                      "23:5: host access: `$fflush`"],
    "host_system.sv": ["7:11: host access: `$system`"],
    "host_plusargs.sv": ["9:9: host access: `$test$plusargs`", "10:9: host access: `$value$plusargs`"],
    "host_dump.sv": ["8:5: host access: `$dumpfile`", "9:5: host access: `$dumpvars`",
                     "10:5: host access: `$dumpports`", "11:5: host access: `$fsdbDumpfile`"],
    "host_dump_comb.sv": ["12:5: host access: `$dumpfile`", "13:5: host access: `$dumpvars`"],
    "host_dpi_import.sv": ["7:3: host access: DPI import"],
    "host_dpi_export.sv": ["10:3: host access: DPI export"],
    "host_other_files.sv": ["9:5: host access: `$sdf_annotate`", "10:5: host access: `$coverage_save`",
                            "11:5: host access: `$input`", "12:5: host access: `$log`",
                            "13:5: host access: `$save`"],
    "host_escaped.sv": ["10:11: escaped identifier"],
    "host_escaped_shadow.sv": ["10:30: escaped identifier", "11:11: escaped identifier",
                               "13:26: escaped identifier"],
    "host_dead_code.sv": ["7:11: host access: `$readmemh`", "10:55: host access: `$fopen`",
                          "17:5: host access: `$readmemh`", "20:13: host access: `$readmemh`"],
    "host_macro.sv": ["3:12: host access: `$readmemh`", "compiler directive or macro `define"],
    "ok_host_words.sv": [],
    "ok_host_comments.sv": [],
    "ok_host_console.sv": [],
    # procedural `for` loops (item 7: the stopgap for three ls-sv loop defects)
    "loop_signed_cond.sv": ["7:49: procedural `for` loop: the condition: the literal `2'd2`",
                            "8:49: procedural `for` loop: the condition: the parameter `P` is "
                            "declared `logic [1:0]`",
                            "9:49: procedural `for` loop: the condition: the literal `1'b1`",
                            "10:53: procedural `for` loop: the condition: the literal `2'd2`"],
    "loop_name_capture.sv": [f"{p}: procedural `for` loop: the iterator `K` has the name of the "
                             "localparam `K` declared at 6:18"
                             for p in ("10:37", "11:37", "12:37", "13:45")],
    "loop_iter_type.sv": ["6:33: procedural `for` loop: the iterator `i` is declared `bit [2:0] i`",
                          "7:33: procedural `for` loop: the iterator `i` is declared `bit [2:0] i`",
                          "8:33: procedural `for` loop: the iterator `i` is declared `bit [1:0] i`",
                          "9:33: procedural `for` loop: the iterator `i` is declared `bit [1:0] i`",
                          "10:33: procedural `for` loop: the iterator `i` is declared `byte i`",
                          "11:20: procedural `for` loop: the iterator `i` is declared "
                          "`int unsigned i`"],
    "loop_header_shape.sv": ["5:51: procedural `for` loop: the step `i[0] = i + 1`",
                             "6:51: procedural `for` loop: the step `i[1]++`",
                             "7:56: procedural `for` loop: a second step `i++`",
                             "8:51: procedural `for` loop: the step `i += d[1:0]`",
                             "9:38: procedural `for` loop: the step `i = i + i`",
                             "10:31: procedural `for` loop: the header declares more than one "
                             "iterator"],
    "loop_module_iter.sv": [f"{p}: procedural `for` loop: the iterator `{n}` is not declared in the "
                            "loop header" for p, n in (("12:12", "i"), ("15:20", "j"), ("16:18", "k"))],
    "ok_loops.sv": [],
}
# The `for` loop fixtures: the defect each one's every finding stands in for (item 7).
LOOP_FIXTURES = {"loop_signed_cond.sv": "cond", "loop_name_capture.sv": "name",
                 "loop_iter_type.sv": "type", "loop_header_shape.sv": "shape",
                 "loop_module_iter.sv": "shape"}
# The positive fixtures that tests/run.py cannot send through `check.py --unproved`: ls-sv refuses
# `initial` and a console task as a statement, so they stop at the design stage. They are gate
# fixtures only (and Yosys must still read them).
GATE_ONLY = {"ok_host_console.sv"}

# System tasks and functions that touch no host resource: console output,
# simulation control, time, and the pure functions. The gate must leave them alone.
# (`$random` and `$urandom` are here because they open no host resource; whether a
# combinational task may use them is the determinism rule's business, not this gate's.)
HARMLESS = ("$display $displayb $displayh $displayo $write $writeb $writeh $writeo $strobe "
            "$strobeb $strobeh $strobeo $monitor $monitorb $monitorh $monitoro $monitoron "
            "$monitoroff $finish $stop $exit $error $warning $info $fatal $time $stime $realtime "
            "$timeformat $printtimescale $clog2 $bits $signed $unsigned $countones $onehot "
            "$onehot0 $isunknown $size $left $right $low $high $increment $dimensions $typename "
            "$sformat $sformatf $swrite $sscanf $sreadmemb $sreadmemh $random $urandom "
            "$urandom_range $itor $rtoi $floor $ceil $sqrt $pow $ln $log10 $exp $sin $cos "
            "$assertoff $asserton $stacktrace $past $rose $fell $stable $sampled").split()

# The clocked rule on blocking writes (item 6): `always_ff` bodies the gate ADMITS under a clock ...
CLOCKED_OK = os.path.join(HERE, "..", "tests", "seq_counter", "ok")
CLOCKED_HEAD = ("module m #(parameter int N = 4) (input logic clk, input logic [N-1:0] d,\n"
                "    output logic [N-1:0] q);\n  logic [3:0] c;\n  integer j;\n")
CLOCKED_FOR_OK = (
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) q[i] <= d[i];",
    "  always_ff @(posedge clk) for (int i = 0; i < 4; i += 1) q[i] <= d[i];",
    "  always_ff @(posedge clk) for (int i = 0; i < N; i = i + 1) q[i] <= d[i];",
    "  always_ff @(posedge clk) for (int i = 0; i < N; ++i) q[i] <= d[i];",
    "  always_ff @(posedge clk) for (int i = N - 1; i >= 0; i--) q[i] <= d[i];",
    "  always_ff @(posedge clk) for (int i = N - 1; i >= 0; i -= 1) q[i] <= d[i];",
    "  always_ff @(posedge clk) for (int i = N - 1; i >= 0; i = i - 1) q[i] <= d[i];",
    "  always_ff @(posedge clk) begin\n    for (int i = 0; i < N; i++)\n"
    "      for (int k = 0; k < 1; k++) q[i + k] <= d[i];\n  end",
)
# ... and the ones it refuses: body -> (line:col, the finding's text after "clocked task: ")
_OUTSIDE = "blocking assignment in `always_ff` to `{}`, declared outside the process"
_ITER = "write to the `for` loop iterator `{}` outside its header step"
_LOCAL = ("blocking assignment in `always_ff` to the block-local variable `{}` (the clock-step "
          "profile, `Stmt2.nbaOnly`, does not admit block-local temporaries yet")
CLOCKED_FOR_REFUSED = {
    "  always_ff @(posedge clk) q = d;": ("5:28", _OUTSIDE.format("q")),
    "  always_ff @(posedge clk) begin q <= d; c = c + 1; end": ("5:42", _OUTSIDE.format("c")),
    "  always_ff @(posedge clk) begin q <= d; c++; end": ("5:42", _OUTSIDE.format("c")),
    "  always_ff @(posedge clk) begin q <= d; ++c; end": ("5:42", _OUTSIDE.format("c")),
    "  always_ff @(posedge clk) begin q <= d; --c; end": ("5:42", _OUTSIDE.format("c")),
    "  always_ff @(posedge clk) begin q <= d; d[0] = 1'b0; end": ("5:42", _OUTSIDE.format("d")),
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) begin q[i] <= d[i]; i = i + 1; end":
        ("5:76", _ITER.format("i")),
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) begin q[i] <= d[i]; i++; end":
        ("5:76", _ITER.format("i")),
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) begin q[i] <= d[i]; ++i; end":
        ("5:76", _ITER.format("i")),
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) begin q[i] <= d[i]; i <= 0; end":
        ("5:76", _ITER.format("i")),
    "  always_ff @(posedge clk) begin logic t; t = d[0]; q[0] <= t; end":
        ("5:43", _LOCAL.format("t")),
    # a block-local `i` inside the body shadows the header's: a temporary, not the iterator
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) begin int i; i = 0; q[0] <= d[0]; end":
        ("5:69", _LOCAL.format("i")),
}

# Item 7, every procedural `for` loop in every process: a head declaring one name of each kind
# (so that an iterator can collide with it), then one body per row (on line 17).
LOOP_HEAD = (
    "package pk; localparam int PK = 1; endpackage\n"
    "module m #(parameter int N = 4, parameter W = 8, parameter integer G = 2,\n"
    "    parameter logic [1:0] P = 2, parameter [3:0] U4 = 3) (\n"
    "    input logic clk, input logic [7:0] d, output logic [7:0] q, r);\n"
    "  localparam L = 3;\n"
    "  localparam int unsigned U = 1;\n"
    "  localparam S = 2'd2;\n"
    "  localparam C = N + 1;\n"
    "  logic [3:0] c;\n"
    "  integer j;\n"
    "  wire w;\n"
    "  typedef logic [1:0] t_t;\n"
    "  typedef enum logic {E0, E1} e_t;\n"
    "  genvar g;\n"
    "  function automatic int f(input int a); return a + L; endfunction\n"
    "  task automatic tk(input int a); endtask\n")
LOOP_LINE = LOOP_HEAD.count("\n") + 1
LOOP_OK = (
    "  always_comb for (int i = 0; i < N; i++) q[i] = d[i];",
    "  always_comb for (integer i = 0; i < 8; i += 1) q[i] = d[i];",
    "  always_comb for (int signed i = W - 1; i >= 0; i--) q[i] = d[i];",
    "  always_comb for (var int i = 7; -1 < i; i = i - 1) q[i] = d[i];",
    "  always_comb for (int i = 0; L + G > i; ++i) q[i] = d[i];",
    "  always_comb for (int i = 2 * (N - 1); i != -2; i -= 2) q[i] = d[i];",
    "  always_comb for (int i = 0; i == 0; i = i + 1) q[i] = d[i];",
    "  always_comb for (int i = 0; i <= (N + 1) * 2 - 3 - i; i++) q[0] = d[i];",
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) for (int k = 0; k < N; k++) q[k] <= d[i];",
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) for (int i = 0; i < 1; i++) q[i] <= d[i];",
    "  function automatic logic [7:0] h(input logic [7:0] x); for (int b = 0; b < 8; b++) h[b] = x[7 - b]; endfunction",
)
LOOP_OK_COMB_ONLY = (
    "  always @* for (int i = 0; i < N; i++) q[i] = d[i];",
    "  initial for (int i = 0; i < N; i++) $display(i);",
)
# body -> [(anchor: the finding is at its first occurrence, defect, text after "procedural `for` loop: ")]
_TY, _NM, _CD, _SH = "type", "name", "cond", "shape"
LOOP_REFUSED = {
    # (c) the iterator's type
    **{f"  always_comb for ({t} i = 0; i < 4; i++) q[i] = d[i];":
       [(t, _TY, f"the iterator `i` is declared `{t} i` (only `int` or `integer`)")]
       for t in ("bit [2:0]", "logic [3:0]", "bit", "logic", "byte", "shortint", "longint",
                 "int unsigned", "integer unsigned", "bit signed [7:0]")},
    "  always_comb for (var i = 0; i < 4; i++) q[0] = d[0];":
        [("var |i", _TY, "the header is declared `var i`")],
    # declared outside the header: at module, block and function scope (the extractor admits all)
    "  always_comb for (j = 0; j < N; j++) q[j] = d[j];":
        [("j = 0", _SH, "the iterator `j` is not declared in the loop header")],
    "  always_ff @(posedge clk) for (j = 0; j < N; j++) q[j] <= d[j];":
        [("j = 0", _SH, "the iterator `j` is not declared in the loop header")],
    "  always @* for (j = 0; j < N; j = j + 1) q[j] = d[j];":
        [("j = 0", _SH, "the iterator `j` is not declared in the loop header")],
    "  always_ff @(posedge clk) begin int i; for (i = 0; i < N; i++) q[i] <= d[i]; end":
        [("i = 0", _SH, "the iterator `i` is not declared in the loop header")],
    "  function automatic logic [7:0] h(input logic [7:0] x); integer i; for (i = 0; i < 8; i = i + 1) h[i] = x[i]; endfunction":
        [("i = 0", _SH, "the iterator `i` is not declared in the loop header")],
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) for (i = 0; i < 1; i++) q[i] <= d[i];":
        [("i = 0; i < 1", _SH, "the iterator `i` is not declared in the loop header")],
    "  always_comb for (; j < 4; j++) q[0] = d[0];": [("for", _SH, "the header declares no iterator")],
    "  always_comb for (int i = 0, k = 0; i < N; i++) q[0] = d[0];":
        [("k = 0", _SH, "the header declares more than one iterator")],
    "  always_comb for (int i; i < 4; i++) q[0] = d[0];": [("i;", _SH, "the iterator `i` has no initial value")],
    # (b) a module-scope name (and a package's)
    **{f"  always_comb for (int {n} = 0; {n} < 4; {n}++) q[0] = d[0];":
       [(f"{n} = 0", _NM, f"the iterator `{n}` has the name of the {what} `{n}` declared at {at}")]
       for n, what, at in (("N", "parameter", "2:26"), ("G", "parameter", "2:68"),
                           ("L", "localparam", "5:14"), ("c", "variable", "9:15"),
                           ("j", "variable", "10:11"), ("w", "net", "11:8"),
                           ("d", "port", "4:40"), ("q", "port", "4:62"), ("clk", "port", "4:17"),
                           ("f", "function", "15:26"), ("tk", "task", "16:18"),
                           ("g", "genvar", "14:10"), ("t_t", "typedef", "12:23"),
                           ("E0", "enum constant", "13:23"), ("PK", "localparam", "1:28"))},
    # (a) the condition (and the initial value, by the same grammar)
    **{f"  always_comb for (int i = 0; i < {e}; i++) q[0] = d[0];": [("i < |" + at, _CD, why)]
       for e, at, why in (
           ("2'd2", "2'd2", "the condition: the literal `2'd2` is sized or based"),
           ("'d2", "'d2", "the condition: the literal `'d2` is sized or based"),
           ("4'sd2", "4'sd2", "the condition: the literal `4'sd2` is sized or based"),
           ("N + 1'b1", "1'b1", "the condition: the literal `1'b1` is sized or based"),
           ("P", "P", "the condition: the parameter `P` is declared `logic [1:0]`"),
           ("U", "U", "the condition: the parameter `U` is declared `int unsigned`"),
           ("U4", "U4", "the condition: the parameter `U4` is declared `[3:0]`"),
           ("S", "S", "the condition: the untyped parameter `S` has the default `2'd2`"),
           ("C", "C", "the condition: the untyped parameter `C` has the default `N + 1`"),
           ("c", "c", "the condition: `c` is not a parameter or localparam that this module "
                      "declares"),
           ("d[3:0]", "d", "the condition: `d[3:0]` (only + - *"),
           ("N / 2", "N", "the condition: `N / 2` (only + - *"),
           ("$clog2(N)", "$", "the condition: `$clog2(N)` (only + - *"),
           ("PK", "PK", "the condition: `PK` is not a parameter or localparam that this module "
                        "declares"),
           ("4294967296", "4", "the condition: the literal `4294967296` does not fit"))},
    "  always_comb for (int i = 0; i < (N << 1); i++) q[0] = d[0];":
        [("N << 1", _CD, "the condition: `N << 1` (only + - *")],
    "  always_comb for (int i = 0; i < N && 1; i++) q[0] = d[0];":
        [("i < N && 1", _CD, "the condition `i < N && 1` is not `i <op> E` or `E <op> i`")],
    "  always_comb for (int i = 0; N > 0; i++) q[0] = d[0];":
        [("N > 0", _CD, "the condition `N > 0` is not `i <op> E` or `E <op> i`")],
    "  always_comb for (int i = 0; i === 4; i++) q[0] = d[0];":
        [("i === 4", _CD, "the condition `i === 4` is not `i <op> E`")],
    "  always_comb for (int i = 0; ; i++) q[0] = d[0];": [("for", _SH, "the header has no condition")],
    "  always_comb for (int i = 0; i < N; i++) for (int k = 0; k < i; k++) q[k] = d[i];":
        [("i; k++", _CD, "the condition: `i` is not a parameter or localparam")],
    "  always_comb begin int N; N = 2; for (int i = 0; i < N; i++) q[i] = d[i]; end":
        [("N; i++", _CD, "the condition: the parameter `N` is declared again in a nested scope")],
    "  always_comb for (int i = 2'd0; i < 4; i++) q[0] = d[0];":
        [("2'd0", _CD, "the initial value: the literal `2'd0` is sized or based")],
    "  always_comb for (int i = d[1:0]; i < 4; i++) q[0] = d[0];":
        [("d[1:0]", _CD, "the initial value: `d[1:0]` (only + - *")],
    "  always_comb for (int i = 0; (i += 1) < N; ) q[i] = d[i];":
        [("for", _SH, "the header has no step"),
         ("(i += 1) < N", _CD, "the condition `(i += 1) < N` is not")],
    # the step
    **{f"  always_comb for (int i = 1; i < N; {st}) q[0] = d[0];":
       [(st, _SH, f"the step `{st}` (only `i++`, `i--`")]
       for st in ("i *= 2", "i = 2 * i", "i = 1 + i", "i += 0", "i -= N", "i += 2'd1", "i = i + i",
                  "c++", "i[0]++", "i[0] = i + 1", "i += d[1:0]", "i <<= 1")},
    "  always_comb for (int i = 0; i < N; i++, c++) q[i] = d[i];":
        [("c++", _SH, "a second step `c++` (one step per loop)")],
    "  always_comb for (int i = 0; i < N; ) q[i] = d[i];": [("for", _SH, "the header has no step")],
    "  always_ff @(posedge clk) for (int i = 0; i < N; i++) for (int k = 0; k < 1; i++) q[i] <= d[i];":
        [("i++) q", _SH, "the step `i++` (only `k++`")],
}


class GateTest(unittest.TestCase):
    def test_fixtures(self):
        for f, want in EXPECT.items():
            canon, findings = srcgate.gate_file(os.path.join(GATE, f))
            if not want:
                self.assertEqual(findings, [], f)
                self.assertIsNotNone(canon)
            else:
                self.assertIsNone(canon, f)
                text = "\n".join(findings)
                for w in want:
                    self.assertIn(w, text, f)

    def test_every_fixture_has_an_expectation(self):
        """A fixture added to score/tests/gate/ without a row in EXPECT would never run."""
        on_disk = {f for f in os.listdir(GATE) if f.endswith(".sv")}
        self.assertEqual(on_disk, set(EXPECT))

    def test_run_py_runs_every_refused_band_fixture(self):
        """tests/run.py (step `attacks`) sends each refused fixture through check.py: the
        host-access fixtures must be on its GATE_FIXTURES list."""
        import ast
        with open(os.path.join(HERE, "..", "tests", "run.py")) as fh:
            tree = ast.parse(fh.read())

        def table(name):
            return next(ast.literal_eval(n.value) for n in tree.body
                        if isinstance(n, ast.Assign) and getattr(n.targets[0], "id", "") == name)
        listed, listed_ok = table("GATE_FIXTURES"), table("GATE_OK_FIXTURES")
        wanted = {f for f in EXPECT if f.startswith("host_")}
        self.assertEqual(wanted - set(listed), set())
        self.assertEqual({f for f in listed if f not in EXPECT}, set())
        # ... and the positive twins go through the whole flow (`check.py --unproved`)
        self.assertEqual({f for f in EXPECT if f.startswith("ok_host_")} - GATE_ONLY, set(listed_ok))

    def test_positive_host_fixtures_are_programs_yosys_reads(self):
        """An `ok_host_*` fixture is the model of a design that must SCORE, so Yosys must be able
        to read its canonical text (a fixture it cannot read passes the gate and then tells a
        reader nothing: `localparam string` is a Yosys syntax error)."""
        import shutil
        import subprocess
        import tempfile
        yosys = os.environ.get("SVGOLF_YOSYS") or shutil.which("yosys")
        self.assertTrue(yosys, "yosys not found (set SVGOLF_YOSYS)")
        ok_fixtures = sorted(f for f in EXPECT if f.startswith("ok_host_"))
        self.assertTrue(ok_fixtures)
        for f in ok_fixtures:
            canon, findings = srcgate.gate_file(os.path.join(GATE, f))
            self.assertEqual(findings, [], f)
            with tempfile.TemporaryDirectory(prefix="srcgate-yosys-") as d:
                path = os.path.join(d, f)
                with open(path, "w", newline="") as fh:
                    fh.write(canon)
                p = subprocess.run([yosys, "-q", "-p", f'read_verilog -sv "{path}"; '
                                    "hierarchy -top band; proc; opt"],
                                   capture_output=True, text=True, timeout=300)
            self.assertEqual(p.returncode, 0, (f, p.stderr[-400:] + p.stdout[-400:]))

    def test_host_table_refuses_every_row(self):
        """One design per name in HOST_SYSTEM_NAMES (and per vendor prefix) and per POSITION
        (an `initial` block, a combinational block, a function nobody calls, a module the top
        does not instantiate): refused, with the name, its family and the principle; also in
        upper case (the match is case-insensitive)."""
        names = sorted(srcgate.HOST_SYSTEM_NAMES) + [p + "x" for p in srcgate.HOST_SYSTEM_PREFIXES]
        self.assertGreaterEqual(len(names), 60)
        head = "module band(input logic a, output logic y);\n"
        positions = (
            ("initial", head + "  initial begin {n}(\"x\"); end\n  assign y = a;\nendmodule\n"),
            ("always_comb", head + "  always_comb begin {n}(\"x\"); y = a; end\nendmodule\n"),
            ("function", head + "  function automatic void f(); {n}(\"x\"); endfunction\n"
                                "  assign y = a;\nendmodule\n"),
            ("other module", "module other; initial {n}(\"x\"); endmodule\n" + head +
                             "  assign y = a;\nendmodule\n"),
        )
        for n in names:
            for spelled in (n, n.upper()):
                for where, template in positions:
                    text = template.replace("{n}", spelled)
                    canon, findings = srcgate.gate_text(text, "t.sv")
                    line, col = srcgate._linecol(text, text.index(spelled))
                    self.assertIsNone(canon, (spelled, where))
                    self.assertEqual(len(findings), 1, (spelled, where, findings))
                    self.assertTrue(
                        findings[0].startswith(f"t.sv:{line}:{col}: host access: `{spelled}`"),
                        (where, findings))
                    self.assertIn("(P-NO-HOST-ACCESS)", findings[0])

    def test_table_has_no_overlap_and_names_are_system_names(self):
        flat = [n for _, _, _, names in srcgate.HOST_FAMILIES for n in names.split()]
        self.assertEqual(len(flat), len(set(flat)))
        self.assertTrue(all(n.startswith("$") for n in flat))
        for fam, what, lrm, names in srcgate.HOST_FAMILIES:
            self.assertTrue(fam and what and lrm and names.split(), fam)

    def test_console_and_pure_tasks_are_left_alone(self):
        for n in HARMLESS:
            text = ("module band(input logic a, output logic y);\n"
                    f"  initial begin {n}(a); end\n  assign y = a;\nendmodule\n")
            canon, findings = srcgate.gate_text(text, "t.sv")
            self.assertEqual(findings, [], n)
            self.assertIsNotNone(canon)

    def test_prose_is_not_a_finding(self):
        """A comment or a string literal naming a refused task is not a use of it, nor is a
        `$`-containing identifier or an escaped identifier that only CONTAINS a `$`."""
        text = ("// $readmemh(\"/etc/hosts\", mem); $fopen $system import \"DPI-C\"\n"
                "/* $dumpfile $value$plusargs */\n"
                "module band(input logic a, output logic y);\n"
                "  localparam string S = \"$readmemh $fopen $system\";\n"
                "  logic \\a$readmemh , t$fopen;\n"
                "  assign y = a;\nendmodule\n")
        canon, findings = srcgate.gate_text(text, "t.sv")
        self.assertEqual(findings, [])

    def test_escaped_dollar_names_are_refused_whatever_they_spell(self):
        for spelled in ("\\$readmemh ", "\\$display ", "\\$clog2 ", "\\$nosuchtask "):
            text = ("module band(input logic a, output logic y);\n"
                    f"  logic {spelled};\n  assign y = a;\nendmodule\n")
            canon, findings = srcgate.gate_text(text, "t.sv")
            self.assertIsNone(canon, spelled)
            self.assertIn("escaped identifier", findings[0])
            self.assertIn("2:9", findings[0])

    def test_dpi_is_refused_at_every_scope(self):
        for where, decl in (("compilation unit", "import \"DPI-C\" function int f(int x);\n"),
                            ("module", "  import \"DPI-C\" context function void g();\n"),
                            ("export", "  function void h(); endfunction\n  export \"DPI\" function h;\n")):
            body = decl if where == "compilation unit" else ""
            inner = "" if where == "compilation unit" else decl
            text = body + ("module band(input logic a, output logic y);\n" + inner
                           + "  assign y = a;\nendmodule\n")
            canon, findings = srcgate.gate_text(text, "t.sv")
            self.assertIsNone(canon, where)
            self.assertIn("host access: DPI", findings[0], where)

    def test_package_import_is_not_dpi(self):
        text = ("package p; localparam int K = 1; endpackage\n"
                "module band(input logic a, output logic y);\n"
                "  import p::*;\n  assign y = a;\nendmodule\n")
        canon, findings = srcgate.gate_text(text, "t.sv")
        self.assertEqual(findings, [])

    def test_canonical_keeps_lines_and_columns(self):
        with open(os.path.join(GATE, "ok_comments.sv")) as fh:
            text = fh.read()
        canon, findings = srcgate.gate_text(text)
        self.assertEqual(findings, [])
        self.assertEqual(len(canon), len(text))
        self.assertEqual(canon.count("\n"), text.count("\n"))
        self.assertNotIn("//", canon)
        self.assertNotIn("/*", canon)
        # every non-comment character is where it was
        _, comments = srcgate.strip_comments(text)
        in_comment = set()
        for off, c in comments:
            in_comment.update(range(off, off + len(c)))
        for i, ch in enumerate(text):
            if i not in in_comment:
                self.assertEqual(canon[i], ch)

    def test_findings_point_at_the_original_text(self):
        """The gate never re-lays-out the text (layout independence of the score
        is the Yosys-side canonical flow's job, score/canon.ys), so a finding's
        `file:line:col` is the submitted file's, comments and blank lines
        included."""
        text = ("// header comment\n\n/* a block\n   comment */\n"
                "module m(input logic a, output logic y);\n"
                "  always_comb unique case (a) 1'b0: y = 0; default: y = 1; endcase\n"
                "endmodule\n")
        canon, findings = srcgate.gate_text(text, "x.sv")
        self.assertIsNone(canon)
        self.assertTrue(any(f.startswith("x.sv:6:15: `unique` qualifier") for f in findings),
                        findings)

    def test_gate_is_idempotent(self):
        with open(os.path.join(GATE, "ok_comments.sv")) as fh:
            canon, _ = srcgate.gate_text(fh.read())
        again, findings = srcgate.gate_text(canon)
        self.assertEqual(findings, [])
        self.assertEqual(again, canon)

    def test_token_stream_check_catches_a_bad_stripper(self):
        """If the comment stripper removed a token, slang's token-stream
        comparison rejects (the stripper is validated, not trusted)."""
        real = srcgate.strip_comments

        def bad(text):
            canon, comments = real(text)
            return canon.replace("a & b", "a    "), comments
        srcgate.strip_comments = bad
        try:
            canon, findings = srcgate.gate_text(
                "module m(input logic a, b, output logic y);\n  assign y = a & b;\nendmodule\n")
        finally:
            srcgate.strip_comments = real
        self.assertIsNone(canon)
        self.assertIn("token stream", findings[0])

    def test_plain_prose_comments_pass(self):
        canon, findings = srcgate.gate_text(
            "// the synthesis-friendly form; see the paper\n"
            "module m(input logic a, output logic y); assign y = a; endmodule\n")
        self.assertEqual(findings, [])

    def test_not_utf8(self):
        import tempfile
        with tempfile.NamedTemporaryFile("wb", suffix=".sv", delete=False) as fh:
            fh.write(b"module m; endmodule // \xff\n")
        try:
            canon, findings = srcgate.gate_file(fh.name)
        finally:
            os.unlink(fh.name)
        self.assertIsNone(canon)
        self.assertIn("not UTF-8", findings[0])

    def test_clocked_for_header_iterator_is_admitted(self):
        """Item 6's one blocking write: a `for` loop's header step on the iterator its header
        declares, in every step form item 7 admits (and nested loops). The positive fixtures
        (tests/seq_counter/ok/) pass the clocked and the combinational gate; the clocked refusal
        fixtures are tests/seq_counter/attacks/ (tests/checker/test_clocked.py runs them), the
        loop-header ones score/tests/gate/loop_*.sv (item 7, every process)."""
        for f in sorted(os.listdir(CLOCKED_OK)):
            path = os.path.join(CLOCKED_OK, f)
            self.assertEqual(srcgate.gate_file(path, clock="clk")[1], [], f)
            self.assertEqual(srcgate.gate_file(path)[1], [], f)
        self.assertEqual(sorted(os.listdir(CLOCKED_OK)), ["for_literal.sv", "for_param.sv"])
        for body in CLOCKED_FOR_OK:
            canon, findings = srcgate.gate_text(CLOCKED_HEAD + body + "\nendmodule\n", "t.sv",
                                                clock="clk")
            self.assertEqual(findings, [], body)
            self.assertIsNotNone(canon)

    def test_clocked_blocking_writes_still_refused(self):
        """Every other blocking write in an `always_ff` (and any write to a loop iterator outside
        its header) is ONE finding, naming why: declared outside the process, the loop's
        iterator, a block-local temporary (not in the clock-step profile yet). The prefix forms
        `++c`/`--c` too (slang's `UnaryPreincrementExpression`). Clocked-only: the header of a
        loop is item 7's (`test_loop_headers_refused`)."""
        for body, (pos, want) in CLOCKED_FOR_REFUSED.items():
            text = CLOCKED_HEAD + body + "\nendmodule\n"
            canon, findings = srcgate.gate_text(text, "t.sv", clock="clk")
            self.assertIsNone(canon, body)
            self.assertEqual(len(findings), 1, (body, findings))
            self.assertTrue(findings[0].startswith(f"t.sv:{pos}: clocked task: {want}"),
                            (body, findings))
            self.assertEqual(srcgate.gate_text(text, "t.sv")[1], [], body)   # clocked-only

    def test_loop_head_alone_passes(self):
        for clock in (None, "clk"):
            self.assertEqual(srcgate.gate_text(LOOP_HEAD + "endmodule\n", "t.sv", clock=clock)[1],
                             [], clock)

    def test_loop_headers_admitted(self):
        """Item 7's admitted shape, in every process kind and in a function, with and without a
        clock (`always @*` and `initial` are refused by the clocked rules, not by item 7)."""
        for body in LOOP_OK + LOOP_OK_COMB_ONLY:
            for clock in ((None, "clk") if body in LOOP_OK else (None,)):
                canon, findings = srcgate.gate_text(LOOP_HEAD + body + "\nendmodule\n", "t.sv",
                                                    clock=clock)
                self.assertEqual(findings, [], (body, clock))
                self.assertIsNotNone(canon)

    def test_loop_headers_refused(self):
        """Item 7 (the stopgap for three ls-sv loop defects) on every other header: the findings
        are exactly the listed ones, at the offending part, naming the reason, the defect it
        stands in for and the admitted shape; the same with a clock (the clocked rule leaves a
        loop header to item 7) unless the process is an `always @*`."""
        for body, want in LOOP_REFUSED.items():
            text = LOOP_HEAD + body + "\nendmodule\n"
            expect = []
            for anchor, defect, why in want:
                ctx, _, tgt = anchor.rpartition("|")
                col = body.index(tgt, body.index(ctx) if ctx else 0) + 1
                expect.append((f"t.sv:{LOOP_LINE}:{col}: procedural `for` loop: ", why, defect))
            for clock in ((None, "clk") if "always @*" not in body else (None,)):
                canon, findings = srcgate.gate_text(text, "t.sv", clock=clock)
                self.assertIsNone(canon, body)
                self.assertEqual(len(findings), len(expect), (body, clock, findings))
                for (pre, why, defect), f in zip(sorted(expect), findings):
                    self.assertTrue(f.startswith(pre + why), (body, clock, f))
                    self.assertIn("svGolf stopgap until ls-sv fixes its `for` loops: "
                                  + srcgate.LOOP_DEFECTS[defect], f)
                    self.assertIn(srcgate.LOOP_ADMITTED, f)

    def test_loop_fixtures_name_their_defect(self):
        """score/tests/gate/loop_*.sv: one finding per refused loop (EXPECT lists them all), each
        naming the defect the fixture is about, with and without a clock."""
        for f, defect in LOOP_FIXTURES.items():
            for clock in (None, "clk"):
                found = [x for x in srcgate.gate_file(os.path.join(GATE, f), clock=clock)[1]
                         if "procedural `for` loop" in x]
                self.assertEqual(len(found), len(EXPECT[f]), (f, clock, found))
                for x in found:
                    self.assertIn(srcgate.LOOP_DEFECTS[defect], x, f)
        self.assertEqual({f for f in EXPECT if f.startswith("loop_")}, set(LOOP_FIXTURES))

    def test_loop_untyped_parameter_and_overrides(self):
        """An untyped parameter takes the type of the value it is given: admitted in E only while
        no instantiation overrides a parameter of its module with anything but an unsized
        decimal literal, and no `defparam` exists."""
        sub = ("module sub #(parameter W = 4) (input logic [7:0] d, output logic [7:0] q);\n"
               "  always_comb for (int i = 0; i < W; i++) q[i] = d[i];\nendmodule\n")
        top = ("module top(input logic [7:0] d, output logic [7:0] q);\n"
               "  sub #({}) u (.d(d), .q(q));\nendmodule\n")
        for over, ok in ((".W(4)", True), ("4", True), (".W(4'd4)", False), (".W(2 + 2)", False),
                         ("4'd4", False)):
            findings = srcgate.gate_text(sub + top.format(over), "t.sv")[1]
            self.assertEqual(findings == [], ok, (over, findings))
            if not ok:
                self.assertIn("the untyped parameter `W` may be given a sized or computed value",
                              findings[0])
        findings = srcgate.gate_text(sub + "module top; sub u (); defparam u.W = 4; endmodule\n",
                                     "t.sv")[1]
        self.assertTrue(findings and "may be given a sized or computed value" in findings[0])
        # an `int` parameter is converted to `int` whatever it is given
        self.assertEqual(srcgate.gate_text(sub.replace("parameter W", "parameter int W")
                                           + top.format(".W(4'd4)"), "t.sv")[1], [])

    def test_ok_loops_is_a_program_yosys_reads(self):
        import shutil
        import subprocess
        yosys = os.environ.get("SVGOLF_YOSYS") or shutil.which("yosys")
        self.assertTrue(yosys, "yosys not found (set SVGOLF_YOSYS)")
        path = os.path.join(GATE, "ok_loops.sv")
        p = subprocess.run([yosys, "-q", "-p", f'read_verilog -sv "{path}"; '
                            "hierarchy -top band; proc; opt"],
                           capture_output=True, text=True, timeout=300)
        self.assertEqual(p.returncode, 0, p.stderr[-400:] + p.stdout[-400:])

    def test_clocked_positive_fixtures_are_programs_yosys_reads(self):
        import shutil
        import subprocess
        yosys = os.environ.get("SVGOLF_YOSYS") or shutil.which("yosys")
        self.assertTrue(yosys, "yosys not found (set SVGOLF_YOSYS)")
        for f, top in (("for_param.sv", "cnt"), ("for_literal.sv", "rev")):
            path = os.path.join(CLOCKED_OK, f)
            p = subprocess.run([yosys, "-q", "-p", f'read_verilog -sv "{path}"; '
                                f"hierarchy -top {top}; proc; opt"],
                               capture_output=True, text=True, timeout=300)
            self.assertEqual(p.returncode, 0, (f, p.stderr[-400:] + p.stdout[-400:]))

    def test_non_ascii_outside_comments(self):
        canon, findings = srcgate.gate_text(
            "module m(input logic a, output logic y); assign y = a; endmodule\n")
        self.assertIsNone(canon)
        self.assertIn("printable ASCII", findings[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
