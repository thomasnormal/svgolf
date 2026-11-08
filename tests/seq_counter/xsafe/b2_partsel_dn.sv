// B2: descending indexed part select data[i -: 2] (bits i down to i-1).
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [7:0] data;
  logic [2:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; data <= 8'b11010010; i <= 3'd7; end
    else begin i <= i - 3'b1; q <= {6'b0, data[i -: 2]}; end
endmodule
