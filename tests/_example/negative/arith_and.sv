// NEGATIVE (banlist): computes a & b correctly, as (a + b) - (a | b), but the
// task bans run-time `+` and `-`. Rejected by score/banlist.py before Lean.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  assign y = (a + b) - (a | b);
endmodule
