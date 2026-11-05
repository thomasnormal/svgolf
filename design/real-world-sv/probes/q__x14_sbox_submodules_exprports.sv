module gf4_mul(input logic [3:0] a, b, output logic [3:0] p);
  assign p = a ^ b;
endmodule
module t (input logic [7:0] x, output logic [7:0] y);
  logic [3:0] p;
  gf4_mul m (.a(x[7:4] ^ x[3:0]), .b(x[3:0]), .p(p));
  assign y = {p, x[3:0]};
endmodule
