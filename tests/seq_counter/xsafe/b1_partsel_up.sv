// B1: ascending indexed part select data[i +: 2] (offset i, width 2). ls-sv's .index uses offset
// i*elemW; if the extractor emits .index data i 2, it reads offset i*2 instead of i.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [7:0] data;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; data <= 8'b11010010; i <= 2'b0; end
    else begin i <= i + 2'b1; q <= {6'b0, data[i +: 2]}; end
endmodule
