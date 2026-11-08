// expect: score: never-loaded register at N=8: `a`, `b`, `u`
// A register loaded only when q - q is nonzero, which it never is, and two registers that copy u and ~u.
// The enable becomes the constant 0 only in the fine stage, after Yosys gave the flop an enable: "Handling
// never-active EN ... (removing D path)"; a and b then have an undefined constant next value, which the
// log prints as "Setting constant 1-bit" (an x), and each read of a and b is resolved separately.
module cnt #(parameter int N = 8) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  logic u, a, b, inc;
  always_ff @(posedge clk) if ((q - q) != 0) u <= rst;
  always_ff @(posedge clk) begin
    a <= u;
    b <= ~u;
  end
  // a | b = 1 for every value u has
  always_comb inc = (a & (q == 200)) | (b & (q == 200)) | !(q == 200);
  always_ff @(posedge clk) begin
    if (rst)     q <= '0;
    else if (en) q <= q + inc;
  end
endmodule
