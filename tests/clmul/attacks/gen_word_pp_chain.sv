// STYLE: word-wide partial products by generate-for (`pp[i] = b[i] ? a << i : '0`), reduced by XOR
// (ibex_alu.sv's `clmul_and_stage`, ycakbas/rv32imafb-core clmul_unit.sv; those hand-unroll a fixed 32-bit tree,
// here the reduction is a chain so that every N works).
// Correct for every N; scored as written. Not yet inside the proof tactics' fragment (word-level `<<` and `?:`).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [2*N-2:0] aw;
  logic [N-1:0][2*N-2:0] pp;
  logic [N:0][2*N-2:0]   acc;
  assign aw = {{(N-1){1'b0}}, a};
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_pp
      assign pp[i]    = b[i] ? (aw << i) : '0;
      assign acc[i+1] = acc[i] ^ pp[i];
    end
  endgenerate
  assign p = acc[N];
endmodule
