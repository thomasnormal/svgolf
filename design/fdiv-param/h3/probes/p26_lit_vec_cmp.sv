module p26_lit_vec_cmp #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [W-1:0] e;
  logic g;
  assign e = a[W-1:0];
  assign g = (e == 5'd3);
  assign q[0] = g;
  assign q[K-1:1] = '0;
endmodule
