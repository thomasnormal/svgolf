// expect: score: never-loaded memory at N=8: `m`
// An unpacked array written only under a condition the pinned flow folds to false (q == 300, q 8 bits at
// N = 8), read at a constant index and decided both ways (finding F1): opt_mem removes the dead write port
// and then the lane ("removing const-x lane"); the netlist holds q at 200, ls-sv counts from every power-up.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic m [0:1];
  logic u, inc;
  always_ff @(posedge clk) if (q == 300) m[q[0]] <= en;
  always_comb u = m[1];
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
