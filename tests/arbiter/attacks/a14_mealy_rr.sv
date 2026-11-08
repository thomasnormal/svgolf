// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A14 a combinational (Mealy) round-robin: gnt = pick(req, mask) with the mask registered, the OpenTitan/pulp shape without an output register.
// Expected (tests/arbiter/sim.py): FAIL MO (outside the kind: the snapshot is not the value on the wire); the statement rejects it by MooreOut.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [N-1:0] mask, mreq;
  always_comb begin
    mreq = req & mask;
    gnt = (mreq != '0) ? (mreq & (~mreq + 1'b1)) : (req & (~req + 1'b1));
  end
  always_ff @(posedge clk) begin
    if (rst) mask <= '1;
    else if (gnt != '0) mask <= ~((gnt << 1) - 1'b1);
  end
endmodule
