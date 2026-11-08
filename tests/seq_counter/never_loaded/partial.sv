// expect: fourstate: Wire cnt.\u [1] is used but has no driver
// A register bit no write reaches (u[1]): no flop at all, an undriven bit (the combinational analogue),
// which fourstate (e) refuses before any synthesis.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic [1:0] u;
  logic inc;
  always_ff @(posedge clk) u[0] <= en;
  always_comb inc = ((u[1] ? 1'b1 : 1'b0) & (q == 200)) | ((u[1] ? 1'b0 : 1'b1) & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
