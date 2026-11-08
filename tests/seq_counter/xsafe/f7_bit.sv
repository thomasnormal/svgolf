// fixture 7: a never-reset 2-state register reaching the output (round 1's h1_bit).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  bit u;
  always_ff @(posedge clk) begin
    u <= u;
    if (rst)     q <= '0;
    else if (u)  q <= '0;
    else if (en) q <= q + 1'b1;
  end
endmodule
