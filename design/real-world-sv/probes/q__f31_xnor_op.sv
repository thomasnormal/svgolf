module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = a ~^ b;
endmodule
