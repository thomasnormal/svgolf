// expect: `wait`
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk) begin wait (en); if (rst) q <= '0; else q <= q + 1'b1; end
endmodule
