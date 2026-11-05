// micro: 2-D packed array with literal dimensions, row write, row read.
module m1_2d_lit (input logic [2:0] x, output logic [2:0] y);
  logic [3:0][2:0] r;
  assign r[0] = x;
  assign r[1] = ~r[0];
  assign y    = r[1];
endmodule
