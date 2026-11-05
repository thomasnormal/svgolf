// As bad_fn_const_args.sv with a power-of-two divisor: Yosys turns `a / 16`
// into a shift, so the backstop sees no `$div`; only the front check (which
// scans the body because it reads `a`) flags it.
module bad_fn_const_args_pow2 (input logic [15:0] a, input logic [15:0] b,
                               output logic [15:0] q);
  function automatic logic [15:0] g(input int k);
    g = a / 16;
  endfunction
  assign q = g(0);
endmodule
