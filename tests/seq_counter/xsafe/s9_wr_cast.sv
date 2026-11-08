module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; i <= 2'b0; end
    else begin i <= i + 2'b1; q[$signed(i)] <= 1'b1; end
endmodule
