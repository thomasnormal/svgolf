module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  logic [N-1:0] pp [2];
  assign pp[0] = a & b;
  assign pp[1] = a | b;
  assign y = pp[0] ^ pp[1];
endmodule
