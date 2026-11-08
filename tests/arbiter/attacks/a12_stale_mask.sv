// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A12 mask round-robin that forgets to update the mask on the wrap-around (unmasked) grant.
// Expected (tests/arbiter/sim.py): FAIL G4 at N >= 2 (after a wrap the lowest requester wins forever).
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [N-1:0] mask, mreq, pick;
  logic wrap;
  always_comb begin
    mreq = req & mask;
    wrap = (mreq == '0);
    pick = !wrap ? (mreq & (~mreq + 1'b1)) : (req & (~req + 1'b1));
  end
  always_ff @(posedge clk) begin
    if (rst) begin
      gnt <= '0;
      mask <= '1;
    end else begin
      gnt <= pick;
      if (pick != '0 && !wrap) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
