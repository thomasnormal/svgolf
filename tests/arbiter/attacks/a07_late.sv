// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A07 a correct round-robin decision, delivered one cycle late (gnt answers the previous entry).
// Expected (tests/arbiter/sim.py): FAIL G2 (grant to a requester that has dropped), G3.
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
  logic [N-1:0] q;
  always_ff @(posedge clk) begin
    if (rst) begin
      gnt <= '0;
      q <= '0;
      mask <= '1;
    end else begin
      q <= pick;
      gnt <= q;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
