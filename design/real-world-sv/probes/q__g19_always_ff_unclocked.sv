module t #(parameter int N = 16) (input logic clk, input logic [N-1:0] a, output logic [N-1:0] y);
  always_ff @(posedge clk) y <= a;
endmodule
