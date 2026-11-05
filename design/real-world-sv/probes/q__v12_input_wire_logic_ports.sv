module t #(parameter int N = 16) (input wire logic [N-1:0] a, b, output wire logic [N-1:0] y);
  assign y = a ^ b;
endmodule
