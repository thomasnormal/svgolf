package pk;
  localparam int W = 8;
endpackage
module t import pk::*; (input logic [W-1:0] a, output logic [W-1:0] y);
  assign y = ~a;
endmodule
