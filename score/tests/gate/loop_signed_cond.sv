// Defect (a) of score/srcgate.py item 7, the measured probes w7, w8, w12 (always_ff) and x1
// (always_comb): ls-sv compares the condition as signed integers where SystemVerilog compares
// unsigned (a sized literal, or a packed-typed parameter, makes `i < E` unsigned: from i = -1
// the tools run no iteration, E runs some). Refused: the sized literal, the packed parameter.
module m #(parameter int N = 4) (input logic clk, input logic [7:0] d, output logic [7:0] q, r);
  localparam logic [1:0] P = 2;
  always_ff @(posedge clk) for (int i = -1; i < 2'd2; i++) q[i + 1] <= d[i + 1];
  always_ff @(posedge clk) for (int i = -1; i < P + N - N; i++) q[i + 1] <= d[i + 1];
  always_ff @(posedge clk) for (int i = -1; i < 1'b1; i++) q <= d;
  always_comb begin r = 8'h00; for (int i = -1; i < 2'd2; i++) r[i + 1] = d[i + 1]; end
endmodule
