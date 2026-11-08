// expect: unproved
// Harmless: k has the constant next value 1 and no reset. Yosys replaces the flop by the constant 1 for
// every reader ("Setting constant 1-bit"; the names-kept run shows a 1, not an x): one value, the power-up
// k = 1. Accepted by the never-loaded rule.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic k;
  always_ff @(posedge clk) k <= 1'b1;
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + k;
  end
endmodule
