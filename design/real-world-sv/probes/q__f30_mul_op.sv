module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-1:0] p);
  assign p = a * b;
endmodule
