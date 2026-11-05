// svGolf task `_example` -- reference solution: N two-input AND gates.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = a & b;
endmodule
