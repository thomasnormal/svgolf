// expect: score: never-loaded register at N=8: `u`
// A register loaded only when q == 300, which an 8-bit q never is: Yosys folds the condition and removes
// the flop ("Handling D = Q ... (removing D path)"). The source-level twin does not see it (the write is
// not u's own value); the scored run's log does.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, inc;
  always_ff @(posedge clk) if (q == 300) u <= en;
  // 1 for u = 0 and for u = 1, so from every power-up the design is the counter
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
