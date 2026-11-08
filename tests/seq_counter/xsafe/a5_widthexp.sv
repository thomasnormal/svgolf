// ATK-5: context-vs-self-determined width. a,b 4-bit; q 8-bit. SV computes a+b in the 8-bit
// assignment context (zero-extend) -> 16. A 4-bit self-determined sum would wrap to 0.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a, b;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'd8; b <= 4'd8; end
    else q <= a + b;
endmodule
