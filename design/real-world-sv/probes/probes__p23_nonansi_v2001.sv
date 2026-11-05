module t(a, b, y);
  parameter N = 8;
  input [N-1:0] a, b;
  output [N-1:0] y;
  reg [N-1:0] y;
  always @(a or b) y = a & b;
endmodule
