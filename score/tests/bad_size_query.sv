// A run-time operand beside a size query: `a / $bits(a)` divides the signal `a` at run time (the query's own
// argument is not read, the left operand is). The front check flags it; the backstop does not (`$bits(a)` is 16 at
// N = 16, a power of two: Yosys turns the division into a shift, as for bad_fn_const_args_pow2.sv).
module bad_size_query #(parameter int N = 16) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  assign y = a / $bits(a);
endmodule
