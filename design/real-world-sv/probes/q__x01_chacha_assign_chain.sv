module t (input logic [31:0] a, b, c, d, output logic [31:0] ra, rd);
  logic [31:0] a1, d1, d2, c1;
  assign a1 = a + b;
  assign d1 = d ^ a1;
  assign d2 = {d1[15:0], d1[31:16]};
  assign c1 = c + d2;
  assign ra = a1;
  assign rd = d2;
endmodule
