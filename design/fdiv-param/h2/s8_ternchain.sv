// H2 style S8: priority encoder as nested ternary chain / if-else-if in always_comb (the other common LZC style).
module s8_ternchain (
  input  logic [10:0] m,
  output logic [3:0]  lz
);
  always_comb begin
    if (m[10]) lz = 4'd0;
    else if (m[9]) lz = 4'd1;
    else if (m[8]) lz = 4'd2;
    else if (m[7]) lz = 4'd3;
    else if (m[6]) lz = 4'd4;
    else if (m[5]) lz = 4'd5;
    else if (m[4]) lz = 4'd6;
    else if (m[3]) lz = 4'd7;
    else if (m[2]) lz = 4'd8;
    else if (m[1]) lz = 4'd9;
    else if (m[0]) lz = 4'd10;
    else lz = 4'd11;
  end
endmodule
