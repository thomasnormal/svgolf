module p07_fill_windows #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  assign q[K-1:P] = '1;
  assign q[P-1:0] = '0;
endmodule
