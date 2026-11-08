// expect: score: never-loaded register at N=8: `m[3]`
// A 4-word array written at a run-time index that reaches words 0 and 1 only ({1'b0, q[0]}), read at the
// constant index 3 and decided both ways: the lane is loaded (words 0 and 1 take en), so opt_mem keeps the
// memory, memory_map builds a flop per word, and word 3's has D = Q ("Handling D = Q on $memory\m[3]...
// (removing D path)"): the register row. The netlist holds q at 200; ls-sv counts.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic m [0:3];
  logic u, inc;
  always_ff @(posedge clk) m[{1'b0, q[0]}] <= en;
  always_comb u = m[3];
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
