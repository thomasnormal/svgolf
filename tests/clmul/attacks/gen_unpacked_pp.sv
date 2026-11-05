// STYLE: partial products and the accumulator as UNPACKED arrays, `logic [2*N-2:0] pp [N]` (ibex_alu.sv's
// `clmul_and_stage[32]`, the survey's clmul probe c01), with the zero extension written as a concatenation.
// Correct for every N. ls-sv does not load parameter-sized unpacked arrays (AGGR).
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [2*N-2:0] aw;
  logic [2*N-2:0] pp  [N];
  logic [2*N-2:0] acc [N+1];
  assign aw = {{(N-1){1'b0}}, a};
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g
      assign pp[i]    = b[i] ? (aw << i) : '0;
      assign acc[i+1] = acc[i] ^ pp[i];
    end
  endgenerate
  assign p = acc[N];
endmodule
