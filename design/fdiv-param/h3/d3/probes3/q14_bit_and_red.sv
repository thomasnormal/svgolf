module q14_bit_and_red #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [EW-1:0] e;
  logic x;
  assign e = {a[K-1:0], 1'b0};
  assign x = ~e[EW-1] & (|e);
  assign q[0] = x;
  assign q[K-1:1] = '0;
endmodule
