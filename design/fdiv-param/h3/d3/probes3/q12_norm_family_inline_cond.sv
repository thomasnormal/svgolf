module q12_norm_family_inline_cond #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [P-1:0][P-1:0] nr;
  logic [P-1:0][EW-1:0] yr;
  assign nr[0] = a[P-1:0];
  assign yr[0] = b[W-1:0];
  genvar i;
  generate
    for (i = 0; i < P - 1; i = i + 1) begin : norm
      assign nr[i+1] = nr[i][P-1] ? nr[i] : (nr[i] << 1);
      assign yr[i+1] = nr[i][P-1] ? yr[i] : (yr[i] - 1);
    end
  endgenerate
  assign q[P-1:0] = nr[P-1];
  assign q[K-1:P] = '0;
endmodule
