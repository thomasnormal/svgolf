// micro: part select of a vector declared with localparam bounds (reads as ArraySel).
module m3_part_lp (input logic [10:0] x, output logic [7:0] y);
  localparam integer W = 11;
  logic [W-1:0] m;
  assign m = x;
  assign y = m[10:3];
endmodule
