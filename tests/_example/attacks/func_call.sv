// svGolf attack (_example), WP-C3: a design that LOADS but that ls-sv cannot run. A
// correct `a & b` written through a user function called from always_comb. The extractor
// accepts it and `load_design_sv2` builds `design.sem`, but the lowered design carries a
// loud Unsupported node (ls-sv has no user function calls): no proof about it can hold, and
// ls-sv's `run2` answers UNSUPPORTED on every input. Before WP-C3 nothing in check.py
// tested for it: it surfaced only as an opaque proof error, or at the postsynth stage
// ("ls-sv does not support this design"). The `design` stage now rejects it, before any
// proof, scoring or leaderboard work, naming the first unsupported construct.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  function automatic logic [N-1:0] both(input logic [N-1:0] x, input logic [N-1:0] z);
    both = x & z;
  endfunction
  always_comb y = both(a, b);
endmodule
