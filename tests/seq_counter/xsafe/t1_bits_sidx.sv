// 2026-11-06 adversarial round, finding F3: a CONSTANT bit select written with $bits of a signed signal
// (sq[$bits(sq) - 1], the sign bit of a signed copy of q). ls-sv folds $bits to 8 and loads a constant
// slice (sq, 7, 1): xsafeB is true. The twin used to read the name inside $bits as a run-time signed
// index and refuse the design before the proof.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic signed [N-1:0] sq;
  logic top;
  always_comb sq = q;
  always_comb top = sq[$bits(sq) - 1];
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + 1'b1;
  end
endmodule
