module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic y);
  wire t1;
  assign t1 = a[0] ^ b[0];
  assign y = t1;
endmodule
