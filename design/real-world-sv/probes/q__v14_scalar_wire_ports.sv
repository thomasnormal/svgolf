module t #(parameter int N = 16) (input wire a, b, output wire y);
  assign y = a ^ b;
endmodule
