// Attack for the task `arbiter` (tasks/arbiter/README.md, attack list; own code).
// A09 rotating priority whose counter wraps at 2^clog2(N) instead of N (phantom slots act as slot 0).
// Expected (tests/arbiter/sim.py): FAIL G4 at N = 3, 5 (not a power of two; G3 too at N = 5); PASS at N = 1, 2, 4, 8, the scoring point included.
// (2026-11-05: written as designs/rotate.sv now is, a scan of `req` padded to 2^clog2(N) bits, instead of
// `req[(32'(p) + k) % N]`: ls-sv refuses the cast, and the source checks refuse a run-time index they cannot
// bound, which stopped the design before the property it breaks. The bug is the same: `p` wraps at 2^clog2(N).)
module arbiter #(parameter int N = 8) (
  input  logic         clk, rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  localparam int PW = (N > 1) ? $clog2(N) : 1;
  logic [PW-1:0] p;
  logic [2**PW-1:0] reqp, pickp;      // padded to 2^PW bits: every PW-bit index is in range
  logic [PW:0] s;
  logic [PW-1:0] idx;
  logic [N-1:0] pick;
  logic found;
  always_comb begin
    reqp = '0;
    reqp[N-1:0] = req;
    pickp = '0;
    found = 1'b0;
    s = '0;
    idx = '0;
    for (int k = 0; k < N; k++) begin
      s = p + k;                        // p + k < 2N <= 2^(PW+1)
      idx = (s >= N) ? s - N : s;       // (p + k) mod N
      if (!found && reqp[idx]) begin
        pickp[idx] = 1'b1;
        found = 1'b1;
      end
    end
    pick = pickp[N-1:0];
  end
  always_ff @(posedge clk) begin
    if (rst) begin
      gnt <= '0;
      p <= '0;
    end else begin
      gnt <= pick;
      p <= p + 1'b1;
    end
  end
endmodule
