// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A01 never grant.
// Expected (tests/arbiter/sim.py): FAIL G3 (work conservation), G4.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  always_ff @(posedge clk) gnt <= '0;
endmodule
