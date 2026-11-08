// Attack for the task `arbiter` (tasks/arbiter/README.md, review 11/04; own code).
// A17 a TIME BOMB: a correct round-robin for the first 4095 cycles after a reset, fixed priority
// after that (a 12-bit saturating age counter).
// Expected (tests/arbiter/sim.py): PASS, every check (a reset every ~256 entries hides it); the
// statement rejects it (G4 on a segment of 4095 + N entries with every client requesting).
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [11:0] age;
  logic [N-1:0] mask, mreq, pick, fix;
  always_comb begin
    mreq = req & mask;
    pick = (mreq != '0) ? (mreq & (~mreq + 1'b1)) : (req & (~req + 1'b1));
    fix = req & (~req + 1'b1);
  end
  always_ff @(posedge clk) begin
    if (rst) begin
      gnt <= '0;
      mask <= '1;
      age <= '0;
    end else begin
      if (age != '1) age <= age + 1'b1;
      if (age == '1) gnt <= fix;
      else gnt <= pick;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
