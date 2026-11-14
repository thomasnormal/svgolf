// tests/cycle: the shift register with every stage in the loop (genvar from 0): sv_mirror and sv_cycle cover it.
module shift0 #(parameter int N = 4, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic [W-1:0] d,
  output logic [W-1:0] q
);
  logic [(N+1)*W-1:0] s;
  always_ff @(posedge clk)
    if (rst) s[0 +: W] <= '0;
    else     s[0 +: W] <= d;
  for (genvar k = 0; k < N; k++) begin : g_stage
    always_ff @(posedge clk)
      if (rst) s[(k+1)*W +: W] <= '0;
      else     s[(k+1)*W +: W] <= s[k*W +: W];
  end
  always_ff @(posedge clk) q <= s[N*W +: W];
endmodule
