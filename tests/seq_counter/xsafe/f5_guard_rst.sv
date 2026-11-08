// fixture 5's price: the same design with b reset (round 1's rule 2 needed this).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic busy, b;
  always_ff @(posedge clk) begin
    if (rst)     b <= 1'b0;
    else if (en) b <= 1'b1;
    if (rst) begin
      q    <= '0;
      busy <= 1'b0;
    end else if (en) begin
      busy <= 1'b1;
      if (busy) begin
        if (b) q <= q + 1'b1;
        else   q <= '0;
      end else q <= q + 1'b1;
    end
  end
endmodule
