// expect: unproved
// Harmless: z has the constant next value 0 and no reset: Yosys replaces the flop by the constant 0 for every
// reader ("Setting constant 0-bit").
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic z;
  always_ff @(posedge clk) z <= 1'b0;
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + 1'b1 + z;
  end
endmodule
