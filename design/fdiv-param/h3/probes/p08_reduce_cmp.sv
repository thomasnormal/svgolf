module p08_reduce_cmp #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  logic e1, e2, e3;
  assign e1 = &a[K-2:T];
  assign e2 = (a[P-1:0] >= b[P-1:0]);
  assign e3 = ~|a[T-1:0];
  assign q[0] = e1; assign q[1] = e2; assign q[2] = e3;
  assign q[K-1:3] = '0;
endmodule
