// expect: unproved
// Harmless: a and b are identical flops (the same D and clock, no reset): Yosys merges them into one
// (opt_merge), so their power-ups are equal, one admissible power-up; every read still reads one value.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic a, b;
  always_ff @(posedge clk) a <= en;
  always_ff @(posedge clk) b <= en;
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + (a == b);
  end
endmodule
