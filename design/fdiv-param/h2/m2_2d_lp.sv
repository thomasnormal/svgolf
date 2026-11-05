// micro: the same with localparam dimensions.
module m2_2d_lp (input logic [2:0] x, output logic [2:0] y);
  localparam integer R = 4;
  localparam integer C = 3;
  logic [R-1:0][C-1:0] r;
  assign r[0] = x;
  assign r[1] = ~r[0];
  assign y    = r[1];
endmodule
