// expect: `always_latch`
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  always_latch if (en) q <= q + 1'b1;
endmodule
