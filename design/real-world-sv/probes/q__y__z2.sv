package pk;
  localparam int W = 8;
endpackage
module t (input logic [pk::W-1:0] a, output logic [pk::W-1:0] y);
  import pk::*;
  assign y = ~a;
endmodule
