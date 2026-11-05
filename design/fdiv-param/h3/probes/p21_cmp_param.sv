module p21_cmp_param #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic g3;
  assign g3 = (a[P-1:0] == P);
  assign q[0] = g3;
  assign q[K-1:1] = '0;
endmodule
