// svGolf attack (_example), LATENT: an x from a function-local variable that is
// read before it is assigned. f(s) returns r, which only `s = 1` assigns: in IEEE
// simulation (Icarus 12, measured 10/28) f(0) is x, the if takes its else branch and y = a & b on
// every input. Yosys inlines f, resolves the unassigned r to 1 and the netlist is
// y = a | b (measured with Yosys 0.53). None of the static rules sees it (no x
// literal, no undriven net: Yosys `check` passes). ls-sv has no user function
// calls yet, so the design loads with an unsupported node, no proof can hold, and
// the post-synthesis check fails closed on it ("ls-sv does not support this
// design"). A PR that adds function calls to ls-sv must add a 4-state rule for
// unassigned locals and return values first (score/fourstate.py).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  function automatic logic f(input logic s);
    logic r;
    if (s) r = 1'b1;
    f = r;
  endfunction
  always_comb
    if (f(a[0])) y = a | b;
    else y = a & b;
endmodule
