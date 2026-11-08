// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A03 always grant client 0.
// Expected (tests/arbiter/sim.py): FAIL G2 (no spurious grant).
// (2026-11-05: the constant 1 is the plain literal `1`, not the cast `N'(1)`: ls-sv refuses casts,
// `ConversionExpression:Explicit`, which stopped the design before the property it breaks.)
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  always_ff @(posedge clk) gnt <= rst ? '0 : 1;
endmodule
