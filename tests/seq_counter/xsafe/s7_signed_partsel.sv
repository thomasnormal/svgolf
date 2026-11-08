module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [7:0] a;
  logic signed [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; a <= 8'b10100110; i <= 2'b0; end
    else begin i <= i + 2'b1; q <= {6'b0, a[i*2 +: 2]}; end
endmodule
