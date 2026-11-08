// expect: score: never-loaded memory at N=8: `m`
// An unpacked array no process writes, read at a constant index and decided both ways (the 2026-11-06
// adversarial round's finding F1): in ls-sv m[1] is one power-up value for every read and the design is the
// counter from every power-up. The pinned flow's opt_mem finds lane 0 never loaded ("removing const-x lane")
// and connects every read to an undefined value before memory_map could build a flop, so opt_dff logs nothing;
// the netlist holds q at 200.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic m [0:1];
  logic u, inc;
  always_comb u = m[1];
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
