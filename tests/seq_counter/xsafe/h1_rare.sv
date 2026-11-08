// H1 (x-optimism), the sampling-evasion member: the reference counter plus `u <= u` (never reset).
// ls-sv keeps `u` x, so `if (!u)` takes the ELSE branch (the reference counter). Yosys folds `u`
// and keeps the THEN branch: a counter that saturates at all-ones instead of wrapping. The two
// differ only from q = 2^N - 1 on, which the deterministic post-synthesis stimulus never reaches.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst) q <= '0;
    else if (!u) begin
      if (&q)      q <= q;
      else if (en) q <= q + 1'b1;
    end
    else if (en) q <= q + 1'b1;
  end
endmodule
