// D2: signed comparison. a signed negative, b signed positive; a < b is true signed, false unsigned.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic signed [3:0] a, b;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= -4'sd2; b <= 4'sd3; end
    else q <= (a < b) ? q + 1'b1 : q;
endmodule
