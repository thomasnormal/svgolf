// expect: unproved
// Harmless: t[0] copies t[1] and nothing reads it; t[1] is q[0], kept inverted. Yosys removes t[0]'s flop and ties
// the bit to x (opt_expr -undriven), keeping the wire for t[1]: the post-synthesis check accepts an unread unknown.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [1:0]   t;
  logic [N-1:0] r;
  always_ff @(posedge clk) t[1] <= rst ? 1'b1 : t[1] ^ en;
  always_ff @(posedge clk) t[0] <= t[1];
  always_ff @(posedge clk) begin
    if (rst)             r <= '0;
    else if (en & ~t[1]) r <= r + 2'd2;
  end
  assign q = r | {{(N-1){1'b0}}, ~t[1]};
endmodule
