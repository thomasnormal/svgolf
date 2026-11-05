package pk;
  localparam int W = 8;
endpackage
module t #(parameter int N = 16) (input logic [pk::W-1:0] a, output logic [pk::W-1:0] y);
  assign y = ~a;
endmodule
