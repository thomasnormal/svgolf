// Run-time equality: allowed in every task (alumacc builds no $alu for it).
module ok_cmp_eq #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic         e, ne, ex, nex
);
  assign e   = a == b;
  assign ne  = a != ~b;
  assign ex  = a === b;
  assign nex = a !== b;
endmodule
