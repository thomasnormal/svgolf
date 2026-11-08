// B4: the `inside` set-membership with a wildcard pattern (==? semantics for x/z in the pattern).
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] s;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; s <= 4'b1010; end
    else begin s <= s + 4'b1; q <= (s inside {4'b1?0?}) ? q + 1'b1 : q; end
endmodule
