module t #(parameter int N = 2) (input logic [N-1:0] a, output logic [N-1:0] y);
  import nopkg::*;
  assign y = a;
endmodule
