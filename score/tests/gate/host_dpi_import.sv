// GATE: rejected (P-NO-HOST-ACCESS). DPI: a call into native code (LRM 35).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  import "DPI-C" pure function int c_fn(input int x);
  assign y = a & b & {N{c_fn(1)[0]}};
endmodule
