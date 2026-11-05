// GATE: rejected. Yosys skips the code between the two pragma comments, slang
// reads it: t is driven for ls-sv and undriven (0 GE) for Yosys.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [N-1:0] t;
// synopsys translate_off
  assign t = a & b;
// synopsys translate_on
  assign y = t;
endmodule
