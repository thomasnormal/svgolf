// tests/cycle: a registered AND with a combinational stage (sv_mirror refuses the always_comb process).
module comb_ff #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t;
  always_comb t = a & b;
  always_ff @(posedge clk) q <= t;
endmodule
