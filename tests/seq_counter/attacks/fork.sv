// expect: `fork` block
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk) fork if (rst) q <= '0; else if (en) q <= q + 1'b1; join
endmodule
