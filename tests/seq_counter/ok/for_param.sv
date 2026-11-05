// The counter, its reset written bit by bit by a PARAMETER-bounded `for` loop whose iterator is
// declared in the loop header: admitted by the clocked gate (score/srcgate.py item 6). The body is
// nonblocking only; E expands the loop per parameter point (Param2.lean `instStmt2 .forLoop`).
// At N = 1 the loop runs once (i = 0).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk)
    if (rst)
      for (int i = 0; i < N; i++) q[i] <= 1'b0;
    else if (en)
      q <= q + 1'b1;
endmodule
