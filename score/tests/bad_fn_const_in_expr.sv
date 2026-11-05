// `g(0)` reads the module signal `a`, so `g(0) / 16` is a run-time division
// (the call is not a constant just because its argument is).
module bad_fn_const_in_expr (input logic [15:0] a, input logic [15:0] b,
                             output logic [15:0] q);
  function automatic logic [15:0] g(input int k);
    g = a;
  endfunction
  assign q = g(0) / 16;
endmodule
