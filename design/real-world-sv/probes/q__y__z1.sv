package pk;
  localparam int W = 8;
endpackage
import pk::*;
module t (input logic [W-1:0] a, output logic [W-1:0] y);
  assign y = ~a;
endmodule
