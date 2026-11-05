module t #(parameter int N = 16) (input logic [N-1:0] a, b, input logic ci, output logic [N:0] t);
  assign t = {1'b0, a} + {1'b0, b} + ci;
endmodule
