// fixture 8: an ordinary case on an unreset selector, with a default arm.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic s;
  always_ff @(posedge clk) begin
    s <= s;
    if (rst) q <= '0;
    else case (s)
      1'b1:    q <= '0;
      default: if (en) q <= q + 1'b1;
    endcase
  end
endmodule
