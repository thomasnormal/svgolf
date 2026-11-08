// 2026-11-06 adversarial round, finding F3: a CONSTANT divisor written with $bits of a signal
// ($bits(q) / $bits(q) = 1 at every N). ls-sv folds each $bits to a literal, so the loaded divisor is a
// nonzero known constant: xsafeB is true. The twin used to read q inside $bits as a run-time divisor.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + ($bits(q) / $bits(q));
  end
endmodule
