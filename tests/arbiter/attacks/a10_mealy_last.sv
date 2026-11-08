// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A10 a correct registered round-robin grant g behind the Mealy output gnt = (req == last) ? g : req, last <= req. Every snapshot shows g.
// Expected (tests/arbiter/sim.py): PASS on every snapshot property, FAIL MO (the silicon view: when req changes, gnt = req before the next edge). The statement rejects it by MooreOut.
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
  logic [N-1:0] g, last;
  always_ff @(posedge clk) begin
    last <= req;
    if (rst) begin
      g <= '0;
      mask <= '1;
    end else begin
      g <= pick;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
  assign gnt = (req == last) ? g : req;
endmodule
