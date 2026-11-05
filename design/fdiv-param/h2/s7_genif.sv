// H2 style S7: conditional generate (if) inside a generate loop, and a 2-D array with a non-affine ("2**level") index.
module s7_genif (
  input  logic [7:0] x,
  output logic       y
);
  logic [14:0] t;
  for (genvar level = 0; level < 3; level++) begin : g_lev
    for (genvar k = 0; k < 2 ** level; k++) begin : g_k
      if (level == 2) begin : g_leaf
        assign t[2 ** level - 1 + k] = x[2 * k] | x[2 * k + 1];
      end else begin : g_node
        assign t[2 ** level - 1 + k] = t[2 ** (level + 1) - 1 + 2 * k] | t[2 ** (level + 1) + 2 * k];
      end
    end
  end
  assign y = t[0];
endmodule
