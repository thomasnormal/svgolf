module half(input logic [31:0] a, b, d, output logic [31:0] ra, rd);
  logic [31:0] a1, d1;
  assign a1 = a + b;
  assign d1 = d ^ a1;
  assign ra = a1;
  assign rd = {d1[15:0], d1[31:16]};
endmodule
module t (input logic [31:0] a, b, c, d, output logic [31:0] ra, rd);
  half h0 (.a(a), .b(b), .d(d), .ra(ra), .rd(rd));
endmodule
