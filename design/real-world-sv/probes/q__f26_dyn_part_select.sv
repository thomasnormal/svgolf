module t #(parameter int N = 16) (input logic [N-1:0] a, input logic [3:0] s, output logic [3:0] y);
  assign y = a[s +: 4];
endmodule
