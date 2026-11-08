// expect: fourstate: Wire cnt.\m[1] is used but has no driver
// An array written only at a constant index (m[0]), read at another (m[1]): Yosys's frontend replaces the
// memory by one register per word ("Replacing memory \m with list of registers"), and the word no write
// reaches is an undriven wire, which fourstate (e) refuses before any synthesis (the combinational analogue).
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic m [0:1];
  logic u, inc;
  always_ff @(posedge clk) m[0] <= en;
  always_comb u = m[1] ^ m[0] ^ m[0];
  always_comb inc = ((u ? 1'b1 : 1'b0) & (q == 200)) | ((u ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
