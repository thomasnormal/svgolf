module q20_concat_cmp_operand #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [P:0] nbx;
  logic x;
  assign nbx = {1'b0, b[P-1:0]};
  assign x = (a[P:0] >= nbx);
  assign q[0] = x;
  assign q[K-1:1] = '0;
endmodule
