// H2 probe B6: result exponent (lines 109-111), as written (concatenation operands of + and -).
module b6_exp (
  input  logic [4:0] xa, xb,
  input  logic [3:0] lza, lzb,
  input  logic       adj,
  output logic [6:0] eoff
);
  assign eoff = {2'b0, xa} + {3'b0, lzb} + 7'd47 - {2'b0, xb} - {3'b0, lza} - {6'b0, adj};
endmodule
