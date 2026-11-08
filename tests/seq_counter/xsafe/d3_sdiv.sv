// D3: signed division truncation toward zero: -7 / 2 = -3 (trunc), not -4 (floor).
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic signed [7:0] a;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= -8'sd7; end
    else q <= a / 2'sd2;
endmodule
