// chacha-like quarter step lowered to SSA assigns, widths through a localparam (the x40 route), fixed size
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
  localparam int W = 8;
  logic [W-1:0] a1, d1, d2, c1;
  assign a1 = x ^ {x[3:0], x[7:4]};
  assign d1 = x ^ a1;
  assign d2 = {d1[3:0], d1[7:4]};
  assign c1 = d2 ^ a1;
  assign y  = c1;
endmodule
