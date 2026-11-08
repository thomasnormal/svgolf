// expect: unproved
// Harmless: a reset state register that cycles 0, 1, 2 and is read through its bits (s[0] & s[1]), not by
// comparisons of the whole register with constants: the fsm pass (which the clocked flow no longer runs) did
// not mark it, and the flow keeps its two flops. From the first reset on s is never 3, so q counts. Accepted.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [1:0] s;
  logic inc;
  always_ff @(posedge clk)
    if (rst) s <= 2'd0;
    else s <= s[1] ? 2'd0 : s + 2'd1;
  always_comb inc = !(q == 200) | !(s[0] & s[1]);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
