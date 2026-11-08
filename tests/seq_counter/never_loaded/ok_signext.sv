// expect: unproved
// Harmless: both bits of w always get the same next value: Yosys keeps one flop for both (wreduce, "Removed
// top 1 bits (of 2) from FF cell"), the power-up with w[1] = w[0].
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [1:0] w;
  always_ff @(posedge clk) w <= {en, en};
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + (w[1] == w[0]);
  end
endmodule
