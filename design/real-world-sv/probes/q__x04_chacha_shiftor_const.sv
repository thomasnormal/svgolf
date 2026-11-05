module t (input logic [31:0] a, b, c, d, output logic [31:0] ra, rd);
  logic [31:0] a1, d1;
  assign a1 = a + b;
  assign d1 = d ^ a1;
  assign ra = a1;
  assign rd = (d1 << 16) | (d1 >> 16);
endmodule
