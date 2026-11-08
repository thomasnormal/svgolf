// expect: score: never-loaded register at N=8: `u`
// warn: register `u` is never loaded
// A never-reset register that only holds its value (u <= u), decided both ways (the txtask-v2 review's
// finding A, ux4_200.sv). Correct in ls-sv from every power-up; the pinned Yosys removes the flop
// ("Handling D = Q ... (removing D path)") and resolves each read of u separately: the netlist holds q at
// 200. Refused at score by the flow's own log; the source-level twin warns before the proof.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, inc;
  always_ff @(posedge clk) u <= u;
  // 1 for u = 0 and for u = 1, so from every power-up the design is the counter
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
