module t #(parameter int N = 1) (input logic [31:0] a, b, c, d, output logic [31:0] ra, rd);
  logic [31:0] a1, d1, d2;
  assign a1 = a + b;
  assign d1 = d ^ a1;
  assign d2 = {d1[15:0], d1[31:16]};
  assign ra = a1;
  assign rd = d2;
endmodule
