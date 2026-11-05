module t #(parameter int N = 16) (input logic [N-1:0] a, b, output reg [N-1:0] y);
  always_comb y = a ^ b;
endmodule
