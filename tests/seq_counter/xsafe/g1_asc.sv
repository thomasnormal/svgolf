// probe: dynamic read of an ASCENDING-range vector. m = 4'b1000 is m[0] = 1 (the leftmost bit).
// i = 0 after reset: IEEE reads the bit labelled 0, which is 1.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [0:3] m;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; m <= 4'b1000; i <= 2'd0; end
    else if (en && m[i]) q <= q + 1'b1;
endmodule
