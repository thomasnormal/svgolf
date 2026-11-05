module t (input [7:0] a, b, output [7:0] y);
  wire [7:0] w;
  assign w = a ^ b;
  assign y = w;
endmodule
