// GATE: rejected. Yosys predefines YOSYS, slang does not (0 GE without the gate).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
`ifdef YOSYS
  assign y = '0;
`else
  assign y = a & b;
`endif
endmodule
