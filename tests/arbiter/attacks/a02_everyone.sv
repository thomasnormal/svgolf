// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A02 grant every requester.
// Expected (tests/arbiter/sim.py): FAIL G1 (mutual exclusion) at N >= 2.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  always_ff @(posedge clk) gnt <= rst ? '0 : req;
endmodule
