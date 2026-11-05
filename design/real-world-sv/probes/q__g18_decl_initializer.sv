module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  logic [N-1:0] w = '0;
  assign y = a | w;
endmodule
