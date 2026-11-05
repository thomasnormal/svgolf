module t #(parameter int N = 32) (input logic [N-1:0] a, b, c, d, output logic [N-1:0] ra, rb, rc, rd);
  logic [N-1:0] a1, d1, d2, c1, b1, b2;
  assign a1 = a + b;
  assign d1 = d ^ a1;
  assign d2 = {d1[15:0], d1[N-1:16]};
  assign c1 = c + d2;
  assign b1 = b ^ c1;
  assign b2 = {b1[19:0], b1[N-1:20]};
  assign ra = a1;
  assign rb = b2;
  assign rc = c1;
  assign rd = d2;
endmodule
