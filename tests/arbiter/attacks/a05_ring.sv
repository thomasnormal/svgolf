// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A05 free-running one-hot token ring, gnt = token (request-ignoring; the SYNTCOMP-minimal simple/round-robin arbiter).
// Expected (tests/arbiter/sim.py): FAIL G2 (grants without requests).
// (2026-11-05: the constant 1 is the plain literal `1`, not the cast `N'(1)`: ls-sv refuses casts,
// `ConversionExpression:Explicit`, which stopped the design before the property it breaks.)
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [N-1:0] tok;
  always_ff @(posedge clk) begin
    if (rst) begin
      tok <= 1;
      gnt <= '0;
    end else begin
      tok <= (tok << 1) | (tok >> (N - 1));
      gnt <= tok;
    end
  end
endmodule
