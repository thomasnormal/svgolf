// expect: unproved
// Harmless: u holds its value except at reset, where it is loaded with 0 (D = Q with a sync reset): u is
// loaded; Yosys replaces it by the constant 0, the power-up u = 0 ("Setting constant 0-bit").
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u;
  always_ff @(posedge clk) if (rst) u <= 1'b0; else u <= u;
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + 1'b1 + u;
  end
endmodule
