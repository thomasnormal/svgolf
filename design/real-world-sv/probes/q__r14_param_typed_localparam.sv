module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam logic [15:0] POLY = 16'h002d;
  assign y = a ^ POLY;
endmodule
