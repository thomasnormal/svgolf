// Rule (d): a query function beside a run-time name is still a run-time index: `v[$bits(v) - 1 - i]` with a
// 3-bit `i` addresses -4..3 of a 4-bit `v` (a 32-bit signed expression), refused.
module query_runtime_index #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2:0] i,
  output logic y
);
  logic [N-1:0] v;
  assign v = a;
  assign y = v[$bits(v) - 1 - i];
endmodule
