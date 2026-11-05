module t #(parameter int N = 16) (input logic en, input logic [N-1:0] a, output logic [N-1:0] y);
  always_latch if (en) y = a;
endmodule
