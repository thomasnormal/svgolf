// ATTACK W2 (rule 2 checks the LEAVES of a decision, not its VALUE): an x born inside the
// condition from known operands. d = q + 2 is 0 exactly at q = 2^N - 2. ls-sv: d / d is 1 when
// d != 0 and all-x when d == 0 (division by zero), so `(d / d) != 1` is 0 or x and the if never
// takes its then branch: the reference counter. The decision's leaves (d, i.e. q) are known in
// every state, so rule 2 holds. The netlist's divider returns all ones for 0 / 0, so it stalls
// at q = 2^N - 2. No task bans run-time `/` (counter, matmul, sorter: empty banlist).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [N-1:0] d;
  assign d = q + 2'd2;
  always_ff @(posedge clk)
    if (rst)                q <= '0;
    else if ((d / d) != 1)  q <= q;
    else if (en)            q <= q + 1'b1;
endmodule
