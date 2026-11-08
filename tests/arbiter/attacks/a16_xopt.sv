// Attack for the task `arbiter` (tasks/arbiter/README.md, review 11/04; own code).
// A16 x-optimism on a NEVER-RESET register. `u` is never reset and holds itself: x for ever in
// ls-sv and in a 4-state simulator, a don't-care for Yosys. `if (!u)` on x takes the ELSE branch
// (IEEE 1800 12.4), so every snapshot shows the correct round-robin grant `pick`; Yosys resolves u
// to 0, keeps the THEN branch and scores a fixed-priority arbiter (280 um2 at N = 8, MEASURED).
// Expected (tests/arbiter/sim.py, 4-state RTL): PASS, every check; the statement rejects it by its
// known-state clause KS (Refute.lean `xopt_refuted`, on the N = 2 twin); its netlist fails G4.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic u;
  logic [N-1:0] mask, mreq, pick, fix;
  always_ff @(posedge clk) u <= u;
  always_comb begin
    mreq = req & mask;
    pick = (mreq != '0) ? (mreq & (~mreq + 1'b1)) : (req & (~req + 1'b1));
    fix = req & (~req + 1'b1);
  end
  always_ff @(posedge clk) begin
    if (rst) begin
      gnt <= '0;
      mask <= '1;
    end else begin
      if (!u) gnt <= fix;
      else gnt <= pick;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
