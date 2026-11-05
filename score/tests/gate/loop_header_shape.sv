// score/srcgate.py item 7 on the header shapes the clocked rule of 5bb5ced8 over-admitted (the
// probes b6, b6b, b7, b8, b9, c1, c2): a step on a select, a non-constant step, `i = i + i`, two
// steps, two iterators. Refused in every process: one iterator, one step `i++`/`i += n`/...
module m #(parameter int N = 4) (input logic clk, input logic [7:0] d, output logic [7:0] q, r);
  always_ff @(posedge clk) for (int i = 0; i < N; i[0] = i + 1) q[i] <= d[i];
  always_ff @(posedge clk) for (int i = 0; i < N; i[1]++) q[i + 4] <= d[i];
  always_ff @(posedge clk) for (int i = 0; i < N; i++, i++) r[i] <= d[i];
  always_ff @(posedge clk) for (int i = 1; i < N; i += d[1:0]) r[i + 4] <= d[i];
  always_comb for (int i = 1; i < N; i = i + i) q[0] = d[0];
  always_comb for (int i = 0, j = 0; i < N; i++) q[1] = d[1];
endmodule
