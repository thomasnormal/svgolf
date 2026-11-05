module t (a, b, y);
  parameter int N = 16;
  input [N-1:0] a, b;
  output [N-1:0] y;
  assign y = a ^ b;
endmodule
