module t #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = a & {N{b[0]}};
endmodule
