// the literal-bound loop (4 iterations) fully unrolled into straight-line SSA assigns, literal shifts
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
  logic [7:0] ae, p__1, p__2, p__3, p__4;
  assign ae  = {4'b0000, x[3], x[2], x[1], x[0]};
  assign p__1 = x[4] ? ae : 8'b00000000;
  assign p__2 = x[5] ? (p__1 ^ (ae << 1)) : p__1;
  assign p__3 = x[6] ? (p__2 ^ (ae << 2)) : p__2;
  assign p__4 = x[7] ? (p__3 ^ (ae << 3)) : p__3;
  assign y = p__4;
endmodule
