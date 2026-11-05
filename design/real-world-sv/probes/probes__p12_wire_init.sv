module t (input [7:0] a, b, output [7:0] y);
  wire [7:0] x = a ^ b;
  wire [7:0] z = x & a;
  assign y = z;
endmodule
