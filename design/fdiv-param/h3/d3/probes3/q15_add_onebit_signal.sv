module q15_add_onebit_signal #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic ez;
  logic [W-1:0] y;
  assign ez = ~|a[W-1:0];
  assign y = a[W-1:0] + ez;
  assign q[W-1:0] = y;
  assign q[K-1:W] = '0;
endmodule
