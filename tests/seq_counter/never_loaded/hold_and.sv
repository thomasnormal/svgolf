// expect: score: never-loaded register at N=8: `u`
// warn: register `u` is never loaded
// A never-loaded register written u & u, its own value after simplification: the pinned flow logs "Handling
// D = Q" (the 2026-11-06 adversarial round, MEASURED, as for u ^ 1'b0, u | 1'b0 and u ? u : u), and the
// source-level twin's advisory recognizes the form.
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  logic u, inc;
  always_ff @(posedge clk) u <= u & u;
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin if (rst) q <= '0; else if (en) q <= q + inc; end
endmodule
