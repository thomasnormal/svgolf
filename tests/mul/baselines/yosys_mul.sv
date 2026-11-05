// Baseline (NOT a legal svGolf entry: run-time `*` is banned): Yosys's own multiplier.
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  assign p = a * b;
endmodule
