// tests/cycle: a family that reads windows at k*k*W of an N*N*W-bit input: the window k*k*W + W <= N*N*W is
// beyond sv_disch (nonlinear in the genvar), so the player gives the window tactic; a `sorry` there is
// refused, never admitted.
module square #(parameter int N = 4, parameter int W = 8) (
  input  logic             clk,
  input  logic [N*N*W-1:0] t,
  output logic [N*W-1:0]   s
);
  for (genvar k = 0; k < N; k++) begin : g_sq
    always_ff @(posedge clk) s[k*W +: W] <= t[k*k*W +: W];
  end
endmodule
