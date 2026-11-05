// svGolf attack (_example): the complementary z constants as `==` operands in an
// `if`. ls-sv: each comparison is x (never true), so the if takes its else
// branch, y = a & b. Yosys drops the z bits: the condition is
// a[1] == 0 || a[1] == 1, always true, and the netlist is a | b. Refused by the
// source gate (an x/z literal digit).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb
    if ((a[1:0] == 2'b0z) || (a[1:0] == 2'b1z)) y = a | b;
    else y = a & b;
endmodule
