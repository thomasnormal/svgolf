// slang's ANALYSIS pass reports `cannot assign to input port` (IEEE 1800-2023 23.3.3.2).
module analysis_input #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  assign a = b;
  assign y = a;
endmodule
