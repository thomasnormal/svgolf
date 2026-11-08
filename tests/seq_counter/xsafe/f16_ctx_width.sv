// Table fixture 16 (attack round 2, finding 1): the context width reaches the operands of `>>`
// (IEEE 1800 §11.6.1, §11.8.2). For N >= 2 the sum a + b is computed at N bits: (1 + 1) >> 1 = 1 and
// the counter counts. At N = 1 it is computed at 1 bit: (1 + 1) wraps to 0 and q holds.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic a, b;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 1'b1; b <= 1'b1; end
    else if (en) q <= q + ((a + b) >> 1);
endmodule
