"""Build the svGolf adaptation of pulp-platform common_cells' cc_rr_arb_tree (with its cc_lzc and cc_pkg)
from the pinned upstream files, by exact, counted text replacements (each one asserted to match
exactly once, so a changed upstream fails loudly). Every change carries its number from the header.

usage: python3.12 -I adapt_A.py UPSTREAM_SRC_DIR OUT.sv [--trim-pkg]
"""
import os
import sys

src, out = sys.argv[1], sys.argv[2]
TRIM_PKG = "--trim-pkg" in sys.argv


def read(n):
    return open(os.path.join(src, n)).read()


def rep(s, a, b, count=1):
    n = s.count(a)
    assert n == count, (n, a)
    return s.replace(a, b)


def cut(s, start, end_incl):
    i = s.index(start)
    j = s.index(end_incl, i) + len(end_incl)
    return s[:i] + s[j:]


# ---------------------------------------------------------------- cc_pkg
pkg = ""   # A9: cc_pkg is not used (its one use, the lzc_mode_e enum, becomes a bit parameter)

# ---------------------------------------------------------------- cc_lzc
lzc = read("cc_lzc.sv")
lzc = rep(lzc, '`include "common_cells/assertions.svh"\n\n', "")                                   # A1
lzc = cut(lzc, "  `ifndef COMMON_CELLS_ASSERTS_OFF\n    `ASSERT_INIT(width_0", "  `endif\n\n")      # A1
lzc = rep(lzc, "  parameter int unsigned Width = 2,", "  parameter int Width = 2,")                 # A6
lzc = rep(lzc, "  localparam int unsigned CntWidth = cc_pkg::idx_width(Width)",
          "  localparam int unsigned CntWidth = (Width > 32'd1) ? $clog2(Width) : 32'd1,\n"
          "  // svGolf A7: NumLevels and the two packed 2-D trees, hoisted from gen_lzc\n"
          "  localparam int unsigned NumLevels = $clog2(Width)")                                # A5, A7
lzc = rep(lzc, "    localparam int unsigned NumLevels = $clog2(Width);\n\n", "")                     # A7
lzc = rep(lzc, "    logic [Width-1:0][NumLevels-1:0] index_lut;\n", "")                               # A8
lzc = rep(lzc, "    logic [2**NumLevels-1:0][NumLevels-1:0] index_nodes /* verilator split_var */;\n", "")  # A8
lzc = rep(lzc, "  if (Width <= 1) begin : gen_degenerate_lzc\n",
          "  logic [Width-1:0][NumLevels-1:0] index_lut;\n"
          "  logic [2**NumLevels-1:0][NumLevels-1:0] index_nodes /* verilator split_var */;\n\n"
          "  if (Width <= 1) begin : gen_degenerate_lzc\n")                                       # A8
lzc = rep(lzc, "module cc_lzc import cc_pkg::*; #(", "module cc_lzc #(")                           # A9
lzc = rep(lzc, "  parameter lzc_mode_e   Mode  = LZC_LEADING_ZERO_CNT,",
          "  parameter bit          Mode  = 1'b1,  // svGolf A9: 1'b1 = LZC_LEADING_ZERO_CNT, 1'b0 = trailing")
lzc = rep(lzc, "if (Mode == LZC_LEADING_ZERO_CNT)", "if (Mode == 1'b1)")                           # A9
lzc = rep(lzc, "for (int unsigned i = 0; i < Width; i++)", "for (int i = 0; i < Width; i++)")      # A6
lzc = rep(lzc, "unsigned'(j) < Width", "j < Width")                                                # A4
lzc = rep(lzc, "assign index_lut[j] = (NumLevels)'(unsigned'(j));", "assign index_lut[j] = j;")      # A4
lzc = rep(lzc, "unsigned'(level) < NumLevels", "level < NumLevels")                                # A4
lzc = rep(lzc, "unsigned'(level) == NumLevels - 1", "level == NumLevels - 1")                      # A4
lzc = rep(lzc, "unsigned'(k) * 2", "k * 2", count=3)                                               # A4
lzc = rep(lzc, "= (NumLevels)'(Width - 1);", "= Width - 1;")                                       # A4
lzc = rep(lzc, "NumLevels > unsigned'(0) ?", "NumLevels > 0 ?", count=2)                           # A4

# ---------------------------------------------------------------- cc_rr_arb_tree
rr = read("cc_rr_arb_tree.sv")
rr = rep(rr, '`include "common_cells/assertions.svh"\n`include "common_cells/registers.svh"\n\n', "")  # A1
rr = cut(rr, "        `ifndef COMMON_CELLS_ASSERTS_OFF\n          `ASSERT(lock,", "        `endif\n\n")  # A1
rr = cut(rr, "    `ifndef COMMON_CELLS_ASSERTS_OFF\n    `ASSERT_INIT(numin_0", "    `endif\n")      # A1
# A3: type parameters -> their packed types
rr = rep(rr, "  /// Data type of the payload, can be overwritten with custom type. Only use of `DataWidth`.\n"
             "  parameter type         data_t     = logic [DataWidth-1:0],\n", "")
rr = rep(rr, "  localparam int unsigned IdxWidth   = (NumIn > 32'd1) ? unsigned'($clog2(NumIn)) : 32'd1,\n"
             "  /// Dependent parameter, do **not** overwrite.\n"
             "  /// Type for defining the arbitration priority and arbitrated index signal.\n"
             "  localparam type         idx_t      = logic [IdxWidth-1:0]\n",
         "  localparam int unsigned IdxWidth   = (NumIn > 32'd1) ? $clog2(NumIn) : 32'd1,\n"
         "  // svGolf A7: NumLevels hoisted from gen_arbiter\n"
         "  localparam int unsigned NumLevels  = $clog2(NumIn)\n")                                 # A3, A4, A7
rr = rep(rr, "  input  idx_t                rr_i,", "  input  logic [IdxWidth-1:0]  rr_i,")
rr = rep(rr, "  input  data_t   [NumIn-1:0] data_i,", "  input  logic    [NumIn-1:0][DataWidth-1:0] data_i,")
rr = rep(rr, "  output data_t               data_o,", "  output logic [DataWidth-1:0] data_o,")
rr = rep(rr, "  output idx_t                idx_o", "  output logic [IdxWidth-1:0]  idx_o")
# A2: reset port
rr = rep(rr, "  /// Asynchronous reset active low.\n  input  logic                rst_ni,",
         "  /// Synchronous reset active high (svGolf A2; upstream: asynchronous, active low, rst_ni).\n"
         "  input  logic                rst_i,")
rr = rep(rr, "  if (NumIn == unsigned'(1)) begin : gen_pass_through", "  if (NumIn == 1) begin : gen_pass_through")  # A4
rr = rep(rr, "    localparam int unsigned NumLevels = unsigned'($clog2(NumIn));\n\n", "")           # A7
# A8: the packed 2-D node arrays at module scope (Yosys); A3: idx_t/data_t spelled out
rr = rep(rr, "    idx_t    [2**NumLevels-2:0] index_nodes /* verilator split_var */; // propagates indices\n"
             "    data_t   [2**NumLevels-2:0] data_nodes  /* verilator split_var */; // propagates data\n", "")
rr = rep(rr, "  // just pass through in this corner case\n",
         "  // svGolf A8: the two packed 2-D node arrays, hoisted from gen_arbiter\n"
         "  logic [2**NumLevels-2:0][IdxWidth-1:0]  index_nodes; // propagates indices\n"
         "  logic [2**NumLevels-2:0][DataWidth-1:0] data_nodes;  // propagates data\n\n"
         "  // just pass through in this corner case\n")
rr = rep(rr, "    idx_t                       rr_q;", "    logic [IdxWidth-1:0]        rr_q;")
rr = rep(rr, "      idx_t rr_d;", "      logic [IdxWidth-1:0] rr_d;")
rr = rep(rr, "        idx_t             upper_idx,   lower_idx,   next_idx;",
         "        logic [IdxWidth-1:0] upper_idx,  lower_idx,   next_idx;")
# A2: the three FFARNC registers, written out with the synchronous reset
rr = rep(rr, "        `FFARNC(lock_q, lock_d, clr_i, '0, clk_i, rst_ni)\n",
         "        always_ff @(posedge clk_i) begin\n"
         "          if (rst_i) lock_q <= '0;\n"
         "          else if (clr_i) lock_q <= '0;\n"
         "          else lock_q <= lock_d;\n"
         "        end\n")
rr = rep(rr, "        `FFARNC(req_q, req_d, clr_i, '0, clk_i, rst_ni)\n",
         "        always_ff @(posedge clk_i) begin\n"
         "          if (rst_i) req_q <= '0;\n"
         "          else if (clr_i) req_q <= '0;\n"
         "          else req_q <= req_d;\n"
         "        end\n")
rr = rep(rr, "      `FFARNC(rr_q, rr_d, clr_i, '0, clk_i, rst_ni)\n",
         "      always_ff @(posedge clk_i) begin\n"
         "        if (rst_i) rr_q <= '0;\n"
         "        else if (clr_i) rr_q <= '0;\n"
         "        else rr_q <= rr_d;\n"
         "      end\n")
rr = rep(rr, ".Mode  ( cc_pkg::LZC_TRAILING_ZERO_CNT )", ".Mode  ( 1'b0 )", count=2)           # A9
# A4: casts
rr = rep(rr, "(idx_t'(i) >  rr_q)", "(i >  rr_q)")
rr = rep(rr, "(idx_t'(i) <= rr_q)", "(i <= rr_q)")
rr = rep(rr, "((rr_q == idx_t'(NumIn-1)) ? '0 : rr_q + 1'b1)", "((rr_q == NumIn-1) ? '0 : rr_q + 1'b1)")
rr = rep(rr, "unsigned'(level) < NumLevels", "level < NumLevels")
rr = rep(rr, "if (unsigned'(level) == NumLevels-1)", "if (level == NumLevels-1)")
rr = rep(rr, "if (unsigned'(l) * 2", "if (l * 2", count=3)
rr = rep(rr, "assign index_nodes[Idx0] = idx_t'(sel);", "assign index_nodes[Idx0] = sel;")
rr = rep(rr, "assign index_nodes[Idx0] = idx_t'('0);", "assign index_nodes[Idx0] = '0;")
rr = rep(rr, "assign data_nodes[Idx0]  = data_t'('0);", "assign data_nodes[Idx0]  = '0;")
rr = rep(rr, "idx_t'({1'b1, index_nodes[Idx1+1][NumLevels-unsigned'(level)-2:0]})",
         "{1'b1, index_nodes[Idx1+1][NumLevels-level-2:0]}")
rr = rep(rr, "idx_t'({1'b0, index_nodes[Idx1][NumLevels-unsigned'(level)-2:0]})",
         "{1'b0, index_nodes[Idx1][NumLevels-level-2:0]}")
# A1 leftovers: the lint/split_var comments are plain comments (stripped by the gate); keep.

HEADER = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "adapt_A_header.txt")).read()
open(out, "w").write(HEADER + lzc + "\n" + rr)
print("wrote", out)
