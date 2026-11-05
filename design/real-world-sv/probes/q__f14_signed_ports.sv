module t #(parameter int N = 16) (input logic signed [N-1:0] a, b, output logic y);
  assign y = a < b;
endmodule
