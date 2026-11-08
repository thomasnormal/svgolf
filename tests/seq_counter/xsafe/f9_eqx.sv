// fixture 9: case equality against an x literal, on an unreset s.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic s;
  always_ff @(posedge clk) begin
    s <= s;
    if (rst)               q <= '0;
    else if (s === 1'bx)   q <= '0;
    else if (en)           q <= q + 1'b1;
  end
endmodule
