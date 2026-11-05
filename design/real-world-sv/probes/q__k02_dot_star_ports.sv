module sub(input logic [7:0] a, b, output logic [7:0] y);
  assign y = a ^ b;
endmodule
module t #(parameter int N = 16) (input logic [7:0] a, b, output logic [7:0] y);
  sub u (.*);
endmodule
