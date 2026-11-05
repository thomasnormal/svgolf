module t #(parameter int N = 16) (input logic c, input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = c ? a : 0;
endmodule
