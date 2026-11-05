module q01_red_in_bitwise #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic x;
  assign x = (&a[K-2:T]) & (|a[T-1:0]);
  assign q[0] = x;
  assign q[K-1:1] = '0;
endmodule
