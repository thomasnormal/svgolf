module seqt(input logic clk, input logic rst_n, input logic srst, input logic en, input logic [3:0] d,
            output logic [3:0] q_plain, output logic [3:0] q_arst, output logic [3:0] q_aset, output logic [3:0] q_srst, output logic [3:0] q_en, output logic q_both);
  always_ff @(posedge clk) q_plain <= d;
  always_ff @(posedge clk or negedge rst_n) if (!rst_n) q_arst <= 4'd0; else q_arst <= d;
  always_ff @(posedge clk or negedge rst_n) if (!rst_n) q_aset <= 4'hF; else q_aset <= d;
  always_ff @(posedge clk) if (srst) q_srst <= 4'd0; else q_srst <= d;
  always_ff @(posedge clk) if (en) q_en <= d;
  logic s_n;
  always_ff @(posedge clk or negedge rst_n or negedge srst) if (!rst_n) q_both <= 1'b0; else if (!srst) q_both <= 1'b1; else q_both <= d[0];
endmodule
