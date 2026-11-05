module t (input logic a, output logic y);
`include "nonexistent.vh"
  assign y = a;
endmodule
