`default_nettype none
module t (input wire [7:0] a, output wire [7:0] y);
  assign y = ~a;
endmodule
`default_nettype wire
