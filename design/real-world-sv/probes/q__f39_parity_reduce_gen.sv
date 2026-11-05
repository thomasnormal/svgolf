module t #(parameter int N = 16) (input logic [N-1:0] a, output logic y);
  assign y = ^a;
endmodule
