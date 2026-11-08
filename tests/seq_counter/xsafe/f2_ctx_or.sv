// F2: context width through bitwise OR. y 5-bit; (a+b) is an operand of | (context-transparent), so
// a+b must be at 5 bits = 16. ls-sv may size it at 4 (self) -> wraps to 0.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a, b;
  logic [4:0] y;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'd8; b <= 4'd8; end
    else begin y <= (a + b) | 5'd0; q <= {3'b0, y}; end
endmodule
