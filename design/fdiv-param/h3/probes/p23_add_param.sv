module p23_add_param #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [W-1:0] y;
  assign y = a[W-1:0] + P;
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;
endmodule
