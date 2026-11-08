// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A11 round-robin whose grant flop has no reset branch (only the mask is reset).
// Expected (tests/arbiter/sim.py): FAIL G0 (x at the reset snapshot).
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [N-1:0] mask, mreq, pick;
  always_comb begin
    mreq = req & mask;
    pick = (mreq != '0) ? (mreq & (~mreq + 1'b1)) : (req & (~req + 1'b1));
  end
  always_ff @(posedge clk) begin
    gnt <= pick;
    if (rst) mask <= '1;
    else if (pick != '0) mask <= ~((pick << 1) - 1'b1);
  end
endmodule
