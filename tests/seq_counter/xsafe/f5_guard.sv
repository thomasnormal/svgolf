// fixture 5: unreset data behind a valid flag. b is never reset; busy (reset) is 1 only after
// a count, which also loads b = 1, so the decision on b runs only when b is known.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic busy, b;
  always_ff @(posedge clk) begin
    if (en) b <= 1'b1;
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
