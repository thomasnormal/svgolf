module q02_cmp_in_bitwise #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic x;
  assign x = (a[P-1:0] >= b[P-1:0]) & a[0];
  assign q[0] = x;
  assign q[K-1:1] = '0;
endmodule
