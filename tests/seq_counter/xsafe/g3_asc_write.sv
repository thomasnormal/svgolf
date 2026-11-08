// probe: dynamic WRITE into an ascending-range vector; t[0] is the leftmost bit.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [0:3] t;
  logic [1:0] k;
  always_comb begin
    t = 4'b0000;
    t[k] = 1'b1;
  end
  always_ff @(posedge clk)
    if (rst) begin q <= '0; k <= 2'd0; end
    else if (en && t == 4'b1000) q <= q + 1'b1;
endmodule
