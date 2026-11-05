// NEGATIVE (wrong function): OR instead of AND. Refuted in Refute.lean by one
// concrete run (N = 1, a = 1, b = 0: y = 1, the task says 0).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = a | b;
endmodule
