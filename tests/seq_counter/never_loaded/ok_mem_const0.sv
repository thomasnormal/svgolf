// expect: unproved
// Harmless: an unpacked array every write of which loads 0, read at a constant index and decided both ways:
// opt_mem connects every read to the constant 0 ("removing const-0 lane"), the power-up with every word 0,
// one value for every read. Accepted by the never-loaded rule.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic m [0:1];
  logic u, inc;
  always_ff @(posedge clk) m[q[0]] <= 1'b0;
  always_comb u = m[1];
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
