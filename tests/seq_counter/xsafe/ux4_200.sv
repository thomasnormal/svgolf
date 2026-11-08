// review4 probe: the counter, correct from every power-up of the never-reset, self-holding u:
// the increment is ((u ? 1 : 0) & hit) | ((u ? 0 : 1) & hit) | !hit = 1 for u = 0 and u = 1.
// hit is q == 200 (rare when large).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  logic inc;
  always_ff @(posedge clk) u <= u;
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
