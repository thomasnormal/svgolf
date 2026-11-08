"""Build the svGolf adaptation of OpenTitan's prim_arbiter_tree from the pinned upstream file, by exact,
counted text replacements (each asserted to match once). Changes 1-4 are described in the header.

usage: python3.12 -I adapt_C.py UPSTREAM/prim_arbiter_tree.sv OUT.sv
"""
import os
import sys

s = open(sys.argv[1]).read()


def rep(a, b):
    global s
    assert s.count(a) == 1, a
    s = s.replace(a, b)


# 1. the assertions: the include, ASSERT_INIT, and the whole assertions section
i = s.index("  ////////////////\n  // assertions //")
j = s.index("endmodule : prim_arbiter_tree")
s = s[:i] + s[j:]
rep('`include "prim_assert.sv"\n\n', "")
rep("  `ASSERT_INIT(CheckNGreaterZero_A, N > 0)\n\n", "")
# 2. synchronous active-high reset
rep("  input rst_ni,\n", "  input rst_i,\n")
rep("    always_ff @(posedge clk_i or negedge rst_ni) begin : p_mask_reg\n      if (!rst_ni) begin\n",
    "    always_ff @(posedge clk_i) begin : p_mask_reg\n      if (rst_i) begin\n")
# 3. packed data port
rep("  input        [DW-1:0]    data_i [N],\n", "  input [N-1:0][DW-1:0]    data_i,\n")
# 4. the packed 2-D trees at module scope
rep("    logic [2**(IdxW+1)-2:0][IdxW-1:0] idx_tree;\n    logic [2**(IdxW+1)-2:0][DW-1:0]   data_tree;\n", "")
rep("  // this case is basically just a bypass\n",
    "  // svGolf change 4: the two packed 2-D trees are declared here, not in gen_normal_case\n"
    "  logic [2**(IdxW+1)-2:0][IdxW-1:0] idx_tree;\n"
    "  logic [2**(IdxW+1)-2:0][DW-1:0]   data_tree;\n\n"
    "  // this case is basically just a bypass\n")
hdr = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "adapt_C_header.txt")).read()
open(sys.argv[2], "w").write(hdr + s)
print("wrote", sys.argv[2])
