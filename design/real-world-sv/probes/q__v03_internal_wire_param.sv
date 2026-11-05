module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  wire [N-1:0] x;
  assign x = a ^ b;
  assign y = x & a;
endmodule
