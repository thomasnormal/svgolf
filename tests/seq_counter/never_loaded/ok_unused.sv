// expect: unproved
// Harmless: d is a register nothing reads: Yosys removes it (opt_clean).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic d;
  always_ff @(posedge clk) d <= en;
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + 1'b1;
  end
endmodule
