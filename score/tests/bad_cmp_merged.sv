// A banned `-` and an ordering comparison on the same operands: alumacc merges
// them into ONE $alu (whose src is the subtraction's). Both are reported: the
// $sub before alumacc, the comparison at its own source location after it.
module bad_cmp_merged #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] d,
  output logic         l
);
  assign d = a - b;
  assign l = a < b;
endmodule
