// B3 (control): data[i*2 +: 2], offset i*2 = i*elemW, which .index models exactly.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [7:0] data;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; data <= 8'b11010010; i <= 2'b0; end
    else begin i <= i + 2'b1; q <= {6'b0, data[i*2 +: 2]}; end
endmodule
