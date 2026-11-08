// Negative design for the task `arbiter` (the universal-correctness audit, 2026-11-06; own code).
// WRONG in silicon: the reference mask round-robin plus a flag `bad` that the reset branch sets from
// the PRE-reset value of a 32-bit register `u` (`if (&u) bad <= 1`); `if (bad)` the grant is fixed
// priority. At the first reset edge ls-sv's x start reads `u` as x, `if (x)` takes the else branch,
// and every run from it is the round-robin; the scored netlist reads the power-up `u` (MEASURED,
// pinned flow, N = 8: 49 flops), and from `u` = all ones its first segment is fixed priority. The
// statement quantifies over every power-up state, the first reset edge included (txtask-v2's
// rule 2): Refute.lean `reset_edge_refuted` refutes it from `u` all ones.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [31:0] u;
  logic bad;
  logic [N-1:0] mask, mreq, pick, fix;
  always_comb begin
    mreq = req & mask;
    pick = (mreq != '0) ? (mreq & (~mreq + 1'b1)) : (req & (~req + 1'b1));
    fix = req & (~req + 1'b1);
  end
  always_ff @(posedge clk) begin
    if (rst) begin
      u <= '0;
      if (&u) bad <= 1'b1;
      else bad <= 1'b0;
      gnt <= '0;
      mask <= '1;
    end else begin
      u <= {u[30:0], ~(u[31] ^ u[21] ^ u[1] ^ u[0])};
      if (bad) gnt <= fix;
      else gnt <= pick;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
