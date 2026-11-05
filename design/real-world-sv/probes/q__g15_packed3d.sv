module t #(parameter int N = 4) (input logic [4:0][4:0][N-1:0] a, output logic [4:0][4:0][N-1:0] y);
  assign y = a;
endmodule
