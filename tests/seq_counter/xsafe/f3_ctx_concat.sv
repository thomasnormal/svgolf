// F3: control. {1'b0, a+b} concatenation makes a+b SELF-determined (concat is NOT context-transparent),
// so a+b wraps at 4 bits in BOTH ls-sv and IEEE -> they agree (both = {1'b0, 4'd0} = 0).
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a, b;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'd8; b <= 4'd8; end
    else q <= {3'b0, a + b};
endmodule
