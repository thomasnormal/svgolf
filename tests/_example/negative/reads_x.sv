// NEGATIVE (unknown values): reads the undriven net `z`, which is x, so
// y = a & b & ~z has x bits wherever a & b is 1. Refuted by one concrete run.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  logic [N-1:0] z;
  assign y = a & b & ~z;
endmodule
