// H2 style S9: leading-one index as a nested ternary chain in ONE assign (dgrid fp16 divider style).
module s9_ternchain (
  input  logic [10:0] m,
  output logic [3:0]  li
);
  assign li = m[10] ? 4'd10 : m[9] ? 4'd9 : m[8] ? 4'd8 : m[7] ? 4'd7 : m[6] ? 4'd6 :
              m[5]  ? 4'd5  : m[4] ? 4'd4 : m[3] ? 4'd3 : m[2] ? 4'd2 : m[1] ? 4'd1 : 4'd0;
endmodule
