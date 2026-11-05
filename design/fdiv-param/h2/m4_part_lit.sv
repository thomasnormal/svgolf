// micro: part select of a vector with literal bounds (reads as the legacy PartSel).
module m4_part_lit (input logic [10:0] x, output logic [7:0] y);
  assign y = x[10:3];
endmodule
