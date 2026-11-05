module p15_bounds #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [K-1:0] x;
  genvar i;
  generate
    for (i = 0; i < W + P - 2; i = i + 1) begin : g
      assign x[i] = a[i] & b[i+1];
    end
  endgenerate
  assign x[K-1:K-2] = '0;
  assign q = x;
endmodule
