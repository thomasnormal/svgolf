module t #(parameter int N = 16) (input bit [N-1:0] a, b, output bit [N-1:0] y);
  assign y = a & b;
endmodule
