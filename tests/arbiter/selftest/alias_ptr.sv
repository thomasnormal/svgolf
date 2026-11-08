// The simulation harness's own regression (tests/arbiter/sim.py, the review's F1, 2026-11-07). WRONG: a
// round-robin over a pointer `ptr` that is never reset and is copied to another variable (`base = ptr`). From
// a power-up ptr >= N it grants nothing (G3), so it is wrong for every N whose 4-bit pointer can hold such a
// value. Before the fix, Yosys's `setundef -init` put the power-up value on the copy `base`, `write_verilog`
// dropped it (an init on a wire), Icarus ran `ptr` from x, and the all-x grant fired none of G0 to G4 and MO:
// the design PASSED. sim.py expects it to FAIL on G3 from a 0/1 power-up, with the self-check XK at 0 (the
// index guard `idx < N` keeps every simulated value known: a read out of range is an x in Icarus, which XK
// would count too; the statement's structural rule 3 refuses the read either way). Not an attack on the
// checker: a test of the harness only. The review's form had no index guard.
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [3:0] ptr;            // never reset: any power-up value
  logic [3:0] base, idx, win;
  logic       found;
  integer i;
  always_comb begin
    base = ptr;
    found = 1'b0; win = 4'd0;
    for (i = 0; i < N; i++) begin
      idx = (base + i < N) ? base + i : base + i - N;
      if (!found && idx < N && req[idx]) begin found = 1'b1; win = idx; end   // x-safe: no read out of range
    end
  end
  always_ff @(posedge clk) begin
    if (rst) gnt <= '0;
    else begin
      gnt <= (found && ptr < N) ? (1 << win) : '0;
      if (found) ptr <= (win + 1 < N) ? win + 1 : 4'd0;
    end
  end
endmodule
