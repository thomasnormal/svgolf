module t #(parameter int N = 16) (input logic [N-1:0] a, b, input logic ci, output logic [N-1:0] s);
  assign s = a + b + ci;
endmodule
