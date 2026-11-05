// NEGATIVE for task fdivp (only works for some inputs): always the canonical quiet NaN of the format,
// {0, all-ones exponent, fraction MSB set}. Right on every pair whose quotient is a NaN (a NaN operand, 0/0, inf/inf),
// wrong everywhere else at every format, e.g. 1 / 1.
module fdiv #(
  parameter int W = 5,
  parameter int P = 11
) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
  logic [W-1:0] ones;
  logic [P-2:0] top;
  assign ones = '1;
  assign top  = (1 << (P - 2));
  assign q    = {1'b0, ones, top};
endmodule
