// fixture 4: a run-time division by a nonzero constant (q / 3 <= q always holds).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk)
    if (rst) q <= '0;
    else if (en) begin
      if ((q / 2'd3) <= q) q <= q + 1'b1;
      else                 q <= '0;
    end
endmodule
