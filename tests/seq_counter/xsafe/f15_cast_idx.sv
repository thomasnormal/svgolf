// Table fixture 15 (attack round 2, finding 2): an unsigned register read through $signed: the same
// behaviour as fixture 12 in IEEE 1800 (the index is -1: x), but ls-sv's lowering drops the cast
// and reads m[3].
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] m;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; m <= 4'b1000; i <= 2'b11; end
    else if (en && m[$signed(i)]) q <= q + 1'b1;
endmodule
