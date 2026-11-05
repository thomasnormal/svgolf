module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] lo, hi);
  logic g;
  assign g = a > b;
  assign lo = g ? b : a;
  assign hi = g ? a : b;
endmodule
