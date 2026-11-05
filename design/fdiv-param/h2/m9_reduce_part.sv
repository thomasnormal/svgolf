// micro: sticky collection: an AND of a bit and the OR-reduction of a part select, `t | (s & (|q[1:0]))`.
module m9_reduce_part (input logic t, s, input logic [3:0] x, output logic y);
  localparam integer W4 = 4;
  logic [W4-1:0] xw;
  assign xw = x;
  assign y = t | (s & (|xw[1:0]));
endmodule
