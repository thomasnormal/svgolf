module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N/2-1:0] y);
  assign y = a[N-1:N/2];
endmodule
