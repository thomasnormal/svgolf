module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = a & (-{{(N-1){1'b0}}, b[0]});
endmodule
