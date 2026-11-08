// probe: dynamic read of a vector whose lsb label is 4. m = 4'b0001 is m[4] = 1; i = 0 after reset,
// i + 3'd4 = 4: IEEE reads the bit labelled 4, which is 1.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [7:4] m;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; m <= 4'b0001; i <= 2'd0; end
    else if (en && m[i + 3'd4]) q <= q + 1'b1;
endmodule
