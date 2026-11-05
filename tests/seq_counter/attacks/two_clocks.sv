// expect: clocked by `clk2`
module cnt #(parameter int N = 8) (
  input  logic clk, clk2, rst, en,
  output logic [N-1:0] q
);
  logic [N-1:0] r;
  always_ff @(posedge clk) if (rst) r <= '0; else if (en) r <= r + 1'b1;
  always_ff @(posedge clk2) q <= r;
endmodule
