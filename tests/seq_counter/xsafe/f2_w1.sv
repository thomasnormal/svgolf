// ATTACK W1 (rule 2 bypassed by a combinational temporary): the probe's h1_rare, with the x
// register read through a blocking temporary that the block overwrites AFTER the decision.
// ls-sv: t = u = x at the `if (!t)`, the if takes the else branch, so lo = 0; then t = 0.
// The settled state has t = 0 and lo = 0, both known, so every decision bit (t, lo, rst, en, q)
// is known in every snapshot and pre-edge state, and u (x for ever) is read by no decision.
// Yosys: lo = !u, u is a self-holding flop with no reset, folded as in h1_rare.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, t, lo;
  always_ff @(posedge clk) u <= u;
  always_comb begin
    t = u;
    if (!t) lo = 1'b1;
    else    lo = 1'b0;
    t = 1'b0;
  end
  always_ff @(posedge clk)
    if (rst) q <= '0;
    else if (lo) begin
      if (&q)      q <= q;
      else if (en) q <= q + 1'b1;
    end
    else if (en) q <= q + 1'b1;
endmodule
