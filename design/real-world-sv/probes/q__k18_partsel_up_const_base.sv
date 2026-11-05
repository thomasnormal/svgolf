module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [3:0] y);
  assign y = a[4 +: 4];
endmodule
