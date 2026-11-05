// svGolf attack (_example), LATENT: the `latch_never.sv` trick with `always @*`
// instead of `always_latch`: `r` is assigned only under a condition that is
// never true, so it keeps its initial x in IEEE simulation (else branch,
// y = a & b), while Yosys infers a never-loaded latch, resolves it to r = 0 and
// scores y = a | b (21.328 GE, measured with Yosys 0.53; `always @*` is not
// `always_comb`, so Yosys's `proc` infers the latch without an error). None of
// the static rules sees it. ls-sv does not run `always @*` today
// (`TimedStatement:ImplicitEventControl`), so the post-synthesis check fails
// closed on it. A PR that adds `always @*` to ls-sv must add a 4-state rule
// for an incompletely assigned variable first (score/fourstate.py).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic r;
  always @* begin
    if (a[0] & ~a[0]) r = 1'b1;
  end
  always @* begin
    if (!r) y = a | b;
    else y = a & b;
  end
endmodule
