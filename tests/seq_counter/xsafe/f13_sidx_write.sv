// Table fixture 13 (attack round 2, finding 2): a SIGNED dynamic write index. After reset i = 2'b11:
// ls-sv writes t[3] (the index read unsigned), so t[3] = 1 and the counter counts; IEEE 1800 reads
// the index as -1, out of [3:0], and the write has no effect, so t = 0 and q holds.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] t;
  logic signed [1:0] i;
  always_comb begin
    t = 4'b0000;
    t[i] = 1'b1;
  end
  always_ff @(posedge clk)
    if (rst) begin q <= '0; i <= 2'b11; end
    else if (en && t[3]) q <= q + 1'b1;
endmodule
