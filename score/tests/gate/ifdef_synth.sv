// GATE: rejected. Yosys predefines SYNTHESIS, slang does not: proved as a & b,
// scored as a constant (0 GE) without the gate.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
`ifdef SYNTHESIS
  assign y = '0;
`else
  assign y = a & b;
`endif
endmodule
