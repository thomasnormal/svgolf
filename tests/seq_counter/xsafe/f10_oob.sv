// fixture 10a: a dynamic read that can leave the range (a is 3 bits, i is 2 bits).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [2:0] a;
  logic [1:0] i;
  always_ff @(posedge clk)
    if (rst) begin
      q <= '0;
      a <= 3'b000;
      i <= 2'd0;
    end else begin
      i <= i + 1'b1;
      if (en) begin
        if (a[i] == 1'b1) q <= '0;
        else              q <= q + 1'b1;
      end
    end
endmodule
