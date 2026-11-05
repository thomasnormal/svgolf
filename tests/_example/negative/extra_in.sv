// NEGATIVE (interface): a hidden extra input `en`. With `en` = 1 it computes
// a & b, but the statement pins the input list to exactly `a`, `b`.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  input  logic         en,
  output logic [N-1:0] y
);
  assign y = en ? (a & b) : '0;
endmodule
