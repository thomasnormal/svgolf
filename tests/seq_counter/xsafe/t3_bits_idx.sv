// 2026-11-06 adversarial round, F3's control: a constant bit select q[$bits(q) - 1] of an unsigned signal
// (the counter's top bit) feeding a flag; both the twin and xsafeB admit it.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic top;
  always_comb top = q[$bits(q) - 1];
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + {{(N-1){1'b0}}, en | top | ~top};
  end
endmodule
