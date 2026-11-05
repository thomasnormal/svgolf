module t #(parameter int N = 16) (input logic en, input logic [N-1:0] a, output tri [N-1:0] y);
  assign y = en ? a : 'z;
endmodule
