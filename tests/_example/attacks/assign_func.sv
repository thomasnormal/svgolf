// svGolf attack (_example), WP-C3: the same loud node reached through a CONTINUOUS
// assignment, not a process body (`assign y = both(a, b)`): the loud node sits in an
// `assign`'s right-hand side. The `design` stage rejects it like func_call.sv.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  function automatic logic [N-1:0] both(input logic [N-1:0] x, input logic [N-1:0] z);
    both = x & z;
  endfunction
  assign y = both(a, b);
endmodule
