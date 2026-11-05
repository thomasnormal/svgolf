module q16_row_red_inline #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [P+2:0][P:0] rr;
  logic [P+1:0] qq;
  logic st0;
  assign rr[0] = {1'b0, a[P-1:0]};
  genvar k;
  generate
    for (k = 0; k < P + 2; k = k + 1) begin : div
      assign qq[k] = rr[k][0];
      assign rr[k+1] = rr[k] << 1;
    end
  endgenerate
  assign st0 = (qq[P+1] & qq[0]) | (|rr[P+2]);
  assign q[0] = st0;
  assign q[K-1:1] = '0;
endmodule
