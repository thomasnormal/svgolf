// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A15 half rate: a correct round-robin that arbitrates only every other cycle.
// Expected (tests/arbiter/sim.py): FAIL G3 (idle cycles under load), G4 at full load (N >= 2).
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
  logic t;
  always_ff @(posedge clk) begin
    if (rst) begin
      gnt <= '0;
      mask <= '1;
      t <= 1'b0;
    end else begin
      t <= !t;
      gnt <= t ? pick : '0;
      if (t && pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
