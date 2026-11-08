// f2 with y reset and a, b moving: the 5-bit sum's carry matters on most cycles.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a, b;
  logic [4:0] y;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'd8; b <= 4'd9; y <= '0; end
    else begin a <= a + 4'd3; b <= b + {3'b0, en}; y <= (a + b) | 5'd0; q <= {3'b0, y}; end
endmodule
