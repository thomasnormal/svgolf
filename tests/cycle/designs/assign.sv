// tests/cycle: a register behind a continuous assignment (sv_mirror refuses the assign).
module assign_ff #(parameter int N = 4) (
  input  logic         clk,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q
);
  logic [N-1:0] t;
  assign t = a | b;
  always_ff @(posedge clk) q <= t;
endmodule
