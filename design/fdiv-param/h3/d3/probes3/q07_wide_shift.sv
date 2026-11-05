module q07_wide_shift #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [EW-1:0] d;
  logic [P:0] qs;
  assign d = {a[K-1:0], 1'b0};
  assign qs = b[P:0] >> d;
  assign q[P:0] = qs;
  assign q[K-1:P+1] = '0;
endmodule
