// W4 (statement-level; the source gate refuses `unique`): a unique case whose two items both
// match only before an edge (m = en at every snapshot; en = 1 after en = 0 before the edge).
module u4 (input logic clk, rst, en, output logic [1:0] q);
  logic m;
  always_ff @(posedge clk) begin
    m <= en;
    if (rst) q <= 2'd0;
    else unique case (1'b1)
      en:      q <= 2'd1;
      !m:      q <= 2'd2;
      default: q <= q;
    endcase
  end
endmodule
