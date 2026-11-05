// micro: a constant shift as an arm of ?: (accepted since gate 3a).
module m8_shift_arm (input logic c, input logic [3:0] x, output logic [3:0] y);
  assign y = c ? (x >> 1) : x;
endmodule
