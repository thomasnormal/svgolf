module q11_inline_mag #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  localparam integer EW = W + P + 1;
  logic [W-1:0] ef;
  logic [P:0] qs;
  logic inc;
  logic [K-2:0] mag;
  assign ef = a[W-1:0];
  assign qs = b[P:0];
  assign inc = a[K-1];
  assign mag = {ef, qs[P-1:1]} + inc;
  assign q[K-2:0] = mag;
  assign q[K-1] = 1'b0;
endmodule
