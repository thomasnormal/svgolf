module q05_fill_arm #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic c;
  assign c = a[0];
  assign q[K-1] = a[K-1];
  assign q[K-2:T] = c ? '1 : b[K-2:T];
  assign q[T-1:0] = '0;
endmodule
