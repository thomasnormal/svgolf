// fixture 1: an unknown temporary overwritten before the decision (t = u; t = 0; if (t)).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, t, lo;
  always_ff @(posedge clk) u <= u;
  always_comb begin
    t = u;
    t = 1'b0;
    if (t) lo = 1'b1;
    else   lo = 1'b0;
  end
  always_ff @(posedge clk)
    if (rst)            q <= '0;
    else if (en && !lo) q <= q + 1'b1;
endmodule
