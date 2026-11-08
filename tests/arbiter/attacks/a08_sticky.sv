// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A08 sticky round-robin: after a grant the priority stays AT the granted client (mask keeps it).
// Expected (tests/arbiter/sim.py): FAIL G4 (a persistent requester hogs) at N >= 2.
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
    if (rst) begin
      gnt <= '0;
      mask <= '1;
    end else begin
      gnt <= pick;
      if (pick != '0) mask <= ~(pick - 1'b1);
    end
  end
endmodule
