module t #(parameter int N = 8) (input logic [N-1:0] a, b, input logic ci, output logic [N-1:0] s, output logic co);
  assign {co, s} = a + b + ci;
endmodule
