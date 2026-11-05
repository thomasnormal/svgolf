// A function called with CONSTANT arguments whose body reads module signals
// is run-time logic: `g(0)` is `a / b`. Both checks flag it.
module bad_fn_const_args (input logic [15:0] a, input logic [15:0] b, output logic [15:0] q);
  function automatic logic [15:0] g(input int k);
    g = a / b;
  endfunction
  assign q = g(0);
endmodule
