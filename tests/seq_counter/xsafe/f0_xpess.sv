// fixture 0: x-pessimism. u is never reset; u ^ u is 0 for every value u can have, so the
// increment is 1 from every power-up (ls-sv's all-x start computes q = x instead).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)     q <= '0;
    else if (en) q <= q + (1'b1 ^ (u ^ u));
  end
endmodule
