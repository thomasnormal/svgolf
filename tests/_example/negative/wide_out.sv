// NEGATIVE (interface): the output is N+1 bits wide. Computes the right bits
// (zero-extended), but the statement pins `y` at exactly N bits.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N:0]   y
);
  assign y = a & b;
endmodule
