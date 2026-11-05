// Defect (c) of score/srcgate.py item 7, the measured probes w1, w2, w3, w10, w11: ls-sv ignores
// the iterator's declared type (a `bit [2:0]` iterator wraps at 8 in SystemVerilog, a `byte` at
// 128, `{i, i}` is 4 bits wide for a `bit [1:0]` iterator; not in E). Refused: every iterator
// type but `int` and `integer`.
module m #(parameter int N = 4) (input logic clk, input logic [7:0] d, output logic [7:0] q, r);
  always_ff @(posedge clk) for (bit [2:0] i = 6; i < 7; i += 3) q[i] <= d[i];
  always_ff @(posedge clk) for (bit [2:0] i = N + 2; i < N + 3; i += 3) q[i] <= d[i];
  always_ff @(posedge clk) for (bit [1:0] i = 1; i < 2; i++) r[3:0] <= {i, i};
  always_ff @(posedge clk) for (bit [1:0] i = 0; i < 3; i++) r[i + 4] <= d[i];
  always_ff @(posedge clk) for (byte i = 100; i < N + 124; i += 30) r[7] <= d[0];
  always_comb for (int unsigned i = 0; i < 1; i++) q[0] = d[0];
endmodule
