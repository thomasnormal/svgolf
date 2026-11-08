// expect: score: never-loaded register at N=8: `u`
// warn: register `u` is never loaded
// A never-loaded register whose every write is its own value under a condition (if (en) u <= u).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, inc;
  always_ff @(posedge clk) if (en) u <= u;
  // 1 for u = 0 and for u = 1, so from every power-up the design is the counter
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
