module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  typedef logic [N-1:0] word_t;
  word_t w;
  assign w = ~a;
  assign y = w;
endmodule
