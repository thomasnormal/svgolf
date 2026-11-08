module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [3:0] a;
  logic signed [1:0] i, j;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 4'b1010; i <= 2'b0; j <= 2'b0; end
    else begin i <= i + 2'sb1; j <= i; q <= {7'b0, a[i + j]}; end
endmodule
