module p20_cmp_lit #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic g1, g2;
  assign g1 = (a[W-1:0] >= 3);
  assign g2 = (a[W-1:0] == 3);
  assign q[0] = g1; assign q[1] = g2;
  assign q[K-1:2] = '0;
endmodule
