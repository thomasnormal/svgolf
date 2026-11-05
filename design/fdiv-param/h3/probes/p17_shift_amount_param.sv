module p17_shift_amount_param #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [P-1:0] x;
  assign x = a[P-1:0] << W;
  assign q = {b[K-1:P], x};
endmodule
