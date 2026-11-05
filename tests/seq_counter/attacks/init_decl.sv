// expect: initializer on the declaration of `r`
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q
);
  logic [N-1:0] r = '0;
  always_ff @(posedge clk) if (rst) r <= '0; else if (en) r <= r + 1'b1;
  assign q = r;
endmodule
