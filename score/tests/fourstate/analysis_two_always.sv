// slang's ANALYSIS pass (not getAllDiagnostics()) reports `multiple-always-assigns`: two always_comb
// writers of one variable (IEEE 1800-2023 9.2.2.2, 9.2.2.4). Decided 2026-11-01: a program the slang driver
// rejects is rejected.
module analysis_two_always #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  always_comb y = a & b;
  always_comb y = a | b;
endmodule
