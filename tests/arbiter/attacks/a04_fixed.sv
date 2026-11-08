// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A04 fixed priority: the lowest requester wins.
// Expected (tests/arbiter/sim.py): FAIL G4 (client N-1 starves) at N >= 2; G0..G3 hold.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  always_ff @(posedge clk) gnt <= rst ? '0 : (req & (~req + 1'b1));
endmodule
