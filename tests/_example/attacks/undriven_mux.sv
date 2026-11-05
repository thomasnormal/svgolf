// svGolf attack (_example): an undriven net in a decision. ls-sv and 4-state
// simulators (Icarus 12, measured 10/28) read
// u as x, so t = x ? 0 : 1 is x and the if takes its else branch: y = a & b.
// Yosys makes the undriven net a don't-care and resolves t to 1: the netlist is
// a | b. Refused by the fourstate stage (Yosys `check`: used but no driver).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic u, t;
  assign t = u ? 1'b0 : 1'b1;
  always_comb
    if (t) y = a | b;
    else y = a & b;
endmodule
