module t (input logic [31:0] a, b, c, d, output logic [31:0] ra, rb, rc, rd);
  localparam int W = 32;
  logic [W-1:0] a1, d1, d2, c1, b1, b2;
  assign a1 = a + b;
  assign d1 = d ^ a1;
  assign d2 = {d1[15:0], d1[W-1:16]};
  assign c1 = c + d2;
  assign b1 = b ^ c1;
  assign b2 = {b1[19:0], b1[W-1:20]};
  assign ra = a1;
  assign rb = b2;
  assign rc = c1;
  assign rd = d2;
endmodule
