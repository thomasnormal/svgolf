// Defect (b) of score/srcgate.py item 7, the measured probes s4, s6, s7 (always_ff) and x2
// (always_comb): ls-sv binds the iterator by NAME in the parameter table, so an iterator `K`
// captures the localparam `K` inside the inlined function (E reads 0..N-1 where the tools read
// 1). Refused: an iterator named like any module-scope name.
module m #(parameter int N = 4) (input logic clk, input logic [7:0] d, output logic [7:0] q, r);
  localparam int K = 1;
  function automatic int f4(); return K; endfunction
  function automatic logic f6(input logic x); f6 = (K == 1); endfunction
  function automatic logic f7(input logic x); return K == 1; endfunction
  always_ff @(posedge clk) for (int K = 0; K < N; K++) q[K] <= (f4() == 1);
  always_ff @(posedge clk) for (int K = 0; K < N; K++) q[K + 4] <= f6(1'b0);
  always_ff @(posedge clk) for (int K = 0; K < N; K++) r[K + 4] <= f7(1'b0);
  always_comb begin r[3:0] = 4'h0; for (int K = 0; K < N; K++) r[K] = f6(1'b0); end
endmodule
