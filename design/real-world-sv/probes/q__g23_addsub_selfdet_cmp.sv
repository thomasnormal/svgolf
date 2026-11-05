module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic y);
  assign y = (a + b) > a;
endmodule
