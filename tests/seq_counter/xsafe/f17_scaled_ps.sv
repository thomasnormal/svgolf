// Over-rejection (attack round 2, finding 5): data[i*2 +: 2] stays in [7:0] for every 2-bit i, but the
// unsized 2 makes i*2 a 32-bit index.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic [7:0] data;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin q <= '0; data <= 8'b01010101; i <= 2'd0; end
    else begin
      i <= i + 2'd1;
      if (en && data[i*2 +: 2] == 2'b01) q <= q + 1'b1;
    end
endmodule
