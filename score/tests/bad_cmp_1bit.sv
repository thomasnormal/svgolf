// A run-time ordering comparison on 1-bit operands: alumacc still builds an
// $alu for it, so a task that bans + or - rejects it (decided 2026-11-05).
module bad_cmp_1bit #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic         g
);
  assign g = a[0] > b[0];
endmodule
