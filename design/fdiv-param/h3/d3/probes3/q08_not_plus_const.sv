module q08_not_plus_const #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [EW-1:0] e, z;
  assign e = {a[K-1:0], 1'b0};
  assign z = ~e + 2;
  assign q[EW-2:0] = z[EW-2:0];
endmodule
