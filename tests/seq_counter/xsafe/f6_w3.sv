// ATTACK W3 (the reset-edge residual): a decision AT the reset edge reads power-up state.
// p is q one cycle late, so after any reset or counting cycle q - p is 0 or 1; q - p == 2 is
// reachable only at power-up. ls-sv: at the first reset q and p are x, the if takes the else
// branch, g = 0; at every later reset q - p is 0 or 1, g = 0. So ls-sv is the reference counter
// and g, p, q are known in every claimed state. Hardware: a 1-cycle reset from a power-up with
// q - p == 2 sets g = 1, and the netlist then counts by 2 until the next reset.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [N-1:0] p;
  logic         g;
  always_ff @(posedge clk)
    if (rst) begin
      q <= '0;
      p <= '0;
      if (q - p == 2'd2) g <= 1'b1;
      else               g <= 1'b0;
    end else begin
      p <= q;
      if (en) q <= q + 1'b1 + g;
    end
endmodule
