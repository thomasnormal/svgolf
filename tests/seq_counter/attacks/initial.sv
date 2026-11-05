// expect: `initial` block
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  initial q = '0;
  always_ff @(posedge clk) if (rst) q <= '0; else if (en) q <= q + 1'b1;
endmodule
