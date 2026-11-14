// tests/cycle: a shift register of N stages of W bits, one always_ff per stage (sv_mirror and sv_cycle cover it).
module shift #(parameter int N = 4, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic [W-1:0] d,
  output logic [W-1:0] q
);
  logic [N*W-1:0] s;
  always_ff @(posedge clk)
    if (rst) s[0 +: W] <= '0;
    else     s[0 +: W] <= d;
  for (genvar k = 1; k < N; k++) begin : g_stage
    always_ff @(posedge clk)
      if (rst) s[k*W +: W] <= '0;
      else     s[k*W +: W] <= s[(k-1)*W +: W];
  end
  always_ff @(posedge clk) q <= s[(N-1)*W +: W];
endmodule
