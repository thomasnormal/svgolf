module p16_down_index #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [P+1:0] ge, qq;
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : g
      assign ge[k] = a[k] & b[k];
      assign qq[P+1-k] = ge[k];
    end
  endgenerate
  assign q[P+1:0] = qq;
  assign q[K-1:P+2] = '0;
endmodule
