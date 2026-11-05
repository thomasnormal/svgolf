module t #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [N:0] y);
  assign y = (N+1)'(a) + (N+1)'(b);
endmodule
