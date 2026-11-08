// Negative design for the task `arbiter` (the universal-correctness audit, 2026-11-06; own code).
// WRONG in silicon: the reference mask round-robin plus a 2-state 32-bit ring `u` that is never reset
// and rotates; `if (&u)` the grant is fixed priority. ls-sv's x start gives a 2-state variable the
// value 0, so `u` stays 0 and every run from it is the round-robin; the scored netlist keeps the 32
// flops of `u` without an initial value (MEASURED, pinned flow, N = 8), and from the power-up
// `u` = all ones it is a fixed-priority arbiter for ever. The statement quantifies over every
// power-up state (txtask-v2's rule 2): Refute.lean `ring_refuted` refutes it from `u` all ones.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  bit [31:0] u;
  logic [N-1:0] mask, mreq, pick, fix;
  always_ff @(posedge clk) u <= {u[30:0], u[31]};
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
      if (&u) gnt <= fix;
      else gnt <= pick;
      if (pick != '0) mask <= ~((pick << 1) - 1'b1);
    end
  end
endmodule
