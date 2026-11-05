module q04_const_left_sub #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [EW-1:0] e, d;
  assign e = {a[K-1:0], 1'b0};
  assign d = 1 - e;
  assign q[EW-2:0] = d[EW-2:0];
endmodule
