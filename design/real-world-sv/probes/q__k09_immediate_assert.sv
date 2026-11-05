module t #(parameter int N = 16) (input logic [7:0] a, output logic [7:0] y);
  assign y = a;
  always_comb assert (N > 0);
endmodule
