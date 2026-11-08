// Table fixture 14 (attack round 2, finding 3): an UNSIGNED dynamic write index that leaves the
// range. After reset k = 3 and t is 3 bits: t[k] is out of range and the write has no effect
// (IEEE 1800 §11.5.1; ls-sv's resolveLhs2; Yosys), so t = 0 and the counter counts.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [2:0] t;
  logic [1:0] k;
  always_comb begin
    t = 3'b000;
    t[k] = 1'b1;
  end
  always_ff @(posedge clk)
    if (rst) begin q <= '0; k <= 2'd3; end
    else if (en && t == 3'b000) q <= q + 1'b1;
endmodule
