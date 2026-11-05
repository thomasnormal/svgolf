module q06_zero_arm #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic c;
  logic [W-1:0] y;
  assign c = a[0];
  assign y = c ? 0 : a[W-1:0];
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;
endmodule
