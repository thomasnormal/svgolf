// svGolf attack (_example), LATENT: an x from a latch that is never enabled.
// `r` is assigned only when `t` is 1, and `t = a[0] & ~a[0]` is always 0, so in
// IEEE simulation `r` keeps its initial x: `!r` is x, the if takes its else
// branch and y = a & b on every input. Yosys resolves the never-loaded latch to
// r = 0, so `!r` is 1 and the netlist is y = a | b (21.328 GE, measured with
// Yosys 0.53). None of the static rules sees it (no x literal; the latch has a
// driver, so Yosys `check` passes). ls-sv does not run `always_latch` today, so
// the design loads with an unsupported process, no proof can hold, and the
// post-synthesis check fails closed on it. A PR that adds `always_latch` to
// ls-sv must add a 4-state rule for a latch's initial x first
// (score/fourstate.py).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic r;
  logic t;
  assign t = a[0] & ~a[0];
  always_latch begin
    if (t) r = 1'b1;
  end
  always_comb begin
    if (!r) y = a | b;
    else y = a & b;
  end
endmodule
