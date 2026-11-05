module t #(parameter int N = 16) (input logic [7:0] a, output logic [7:0] y);
  const logic [7:0] K = 8'h1b;
  assign y = a ^ K;
endmodule
