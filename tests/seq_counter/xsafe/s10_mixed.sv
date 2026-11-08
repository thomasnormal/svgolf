module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a;
  logic signed [1:0] i;
  logic [1:0] u;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'b1010; i <= 2'b0; u <= 2'b0; end
    else begin i <= i + 2'b1; q <= {7'b0, a[i + u]}; end
endmodule
