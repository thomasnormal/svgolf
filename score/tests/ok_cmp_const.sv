// Ordering comparisons over parameters and genvars only: Yosys folds them as
// constants, no cell is left, so a task that bans + or - allows them.
module ok_cmp_const #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y, z,
  output logic         w
);
  localparam bit WIDE = N > 8;
  if (N >= 4) begin : g_big
    assign y = WIDE ? a ^ b : a & b;
  end else begin : g_small
    assign y = a | b;
  end
  for (genvar i = 0; i < N; i++) begin : g_z
    assign z[i] = (i < N / 2) ? a[i] : b[i];
  end
  assign w = (N <= 32) ? a[0] : b[0];
endmodule
