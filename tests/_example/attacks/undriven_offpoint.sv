// ATTACK (the universal-correctness audit, 2026-11-06): `undriven_mux.sv`'s x source, present only AWAY from the
// scoring point. `u` has a driver only at N = 16 (a generate-if), so at every other N it is used but undriven: x in
// ls-sv, where `t = u ? 0 : 1` is x and `if (t)` takes the else branch (`y = a & b` at every N: the statement holds),
// and a don't-care to Yosys, whose N = 8 netlist computes `a | b` (measured by the audit: 0xC3, 0xA5 gives 0xE7).
// At N = 16 every stage passes it, the full post-synthesis check included. Refused since 2026-11-06, when the
// `fourstate` stage runs at every point the checker probes (here N = 1, the first probe point after the scoring
// point), not only at the scoring point.
module band #(parameter int N = 16) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic u, t;
  generate
    if (N == 16) begin : g_drv
      assign u = 1'b1;
    end
  endgenerate
  assign t = u ? 1'b0 : 1'b1;
  always_comb
    if (t) y = a | b;
    else   y = a & b;
endmodule
