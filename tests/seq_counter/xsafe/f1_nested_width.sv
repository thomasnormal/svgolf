// F1: nested context width. y is 5 bits; (a+b) is the context-determined left operand of >>, so a+b
// must be computed at 5 bits (=16), then >>1 = 8. A 4-bit self-determined add wraps to 0 -> >>1 = 0.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a, b;
  logic [4:0] y;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'd8; b <= 4'd8; end
    else begin y <= (a + b) >> 1; q <= {3'b0, y}; end
endmodule
