// slang's ANALYSIS pass reports `mixed-var-assigns`: continuous and procedural assignments to one variable
// (IEEE 1800-2023 6.5).
module analysis_mixed #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  assign y = a & b;
  always_comb y = a | b;
endmodule
