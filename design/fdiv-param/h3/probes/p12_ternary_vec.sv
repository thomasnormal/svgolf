module p12_ternary_vec #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic c;
  logic [W-1:0] x;
  assign c = a[0];
  assign x = c ? a[W-1:0] : b[W-1:0];
  assign q[W-1:0] = x;
  assign q[K-1:W] = '0;
endmodule
