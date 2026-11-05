module t #(parameter int N = 16, parameter logic [15:0] POLY = 16'h002d) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = a ^ N'(POLY);
endmodule
