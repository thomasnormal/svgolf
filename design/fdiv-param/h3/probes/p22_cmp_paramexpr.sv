module p22_cmp_paramexpr #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic g1;
  assign g1 = (a[W-1:0] >= P + 1);
  assign q[0] = g1;
  assign q[K-1:1] = '0;
endmodule
