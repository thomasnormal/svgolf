// A `for` loop whose iterator is declared OUTSIDE its header (a module-level `integer`), in an
// `always_ff`, an `always_comb` and an `always @*`: refused by item 7 of score/srcgate.py in every
// process (the expansion never writes the variable, and its declared type is not read). Moved
// here from tests/seq_counter/attacks/ (it is no longer a clocked-only refusal).
module cnt #(parameter int N = 8) (
  input  logic clk, rst, en,
  output logic [N-1:0] q, r, s
);
  integer i, j, k;
  always_ff @(posedge clk)
    if (rst)
      for (i = 0; i < N; i++) q[i] <= 1'b0;
    else if (en)
      q <= q + 1'b1;
  always_comb for (j = 0; j < N; j = j + 1) r[j] = q[N - 1 - j];
  always @* for (k = 0; k < N; k = k + 1) s[k] = q[k];
endmodule
