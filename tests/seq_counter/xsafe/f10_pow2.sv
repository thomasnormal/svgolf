// fixture 10b: a full-width index into a power-of-two array (a is 4 bits, i is 2 bits).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [3:0] a;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin
      q <= '0;
      a <= 4'b0000;
      i <= 2'd0;
    end else begin
      i <= i + 1'b1;
      if (en) begin
        if (a[i] == 1'b1) q <= '0;
        else              q <= q + 1'b1;
      end
    end
endmodule
