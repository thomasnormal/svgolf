// D4: mixed signed/unsigned: per IEEE 11.8.1 if any operand is unsigned the whole expression is
// unsigned. a signed, u unsigned; (a + u) then compared. Here the subtraction a - 1'b1 with a small.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic signed [3:0] a;
  logic [0:0] u;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'sd0; u <= 1'b1; end
    else q <= ((a - u) < 0) ? q + 1'b1 : q;   // a-u unsigned -> never < 0
endmodule
