// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A13 the round-robin with an ASYNCHRONOUS reset.
// Expected (tests/arbiter/sim.py): FAIL MO at reset entries (gnt changes when rst rises, mid-period); the statement refuses it structurally (ClockedBy clk none).
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
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      gnt <= '0;
      mask <= '1;
    end else begin
      gnt <= pick;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
