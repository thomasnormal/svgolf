// `always y = a;` never advances time: slang's ANALYSIS pass reports it (IEEE 1800-2023 9.2.2.1,
// a simulation deadlock); Yosys reads a wire.
module analysis_always_notime #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  always y = a;
endmodule
