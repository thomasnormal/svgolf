module p27_div_family #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  logic [P:0] nbx;
  logic [P+2:0][P:0] rr;
  logic [P+1:0][P:0] dd;
  logic [P+1:0] ge, qq;
  assign nbx = {1'b0, b[P-1:0]};
  assign rr[0] = {1'b0, a[P-1:0]};
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : g
      assign ge[k] = (rr[k] >= nbx);
      assign dd[k] = rr[k] - nbx;
      assign qq[P+1-k] = ge[k];
      assign rr[k+1] = ge[k] ? (dd[k] << 1) : (rr[k] << 1);
    end
  endgenerate
  assign q[P+1:0] = qq;
  assign q[K-1:P+2] = '0;
endmodule
