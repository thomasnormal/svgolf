// ATK-6: shift by a known amount >= width. (1 << amt) with amt from a register.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] amt;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; amt <= 4'd9; end
    else q <= (8'd1 << amt);
endmodule
