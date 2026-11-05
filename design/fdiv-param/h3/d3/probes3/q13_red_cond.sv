module q13_red_cond #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [W-1:0] y;
  assign y = (|a[W-1:0]) ? a[W-1:0] : 1;
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;
endmodule
