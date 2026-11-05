// A LITERAL-bounded `for` loop in `always_ff` whose iterator is declared in the loop header, with
// the `i += k` step: admitted by the clocked gate (score/srcgate.py item 6). The extractor unrolls a
// literal-bounded loop itself. A gate fixture with its own module (not the task's `cnt`).
module rev (
  input  logic       clk,
  input  logic [3:0] d,
  output logic [3:0] q
);
  always_ff @(posedge clk)
    for (int i = 0; i < 4; i += 1) q[i] <= d[3 - i];
endmodule
