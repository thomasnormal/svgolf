// C3 (control): unsigned write index, out of range for some values. q is 8 bits, idx 4 bits (0..15):
// writes to idx 8..15 are no-ops in both ls-sv and Yosys.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] idx;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; idx <= 4'd0; end
    else begin idx <= idx + 4'b1; q[idx] <= 1'b1; end
endmodule
