// EQUIVALENT (must pass): rotating priority. A mod-N counter `p` advances EVERY cycle, whatever is
// granted; the first requester at or above p (cyclically) wins. Fair within N cycles, a different
// policy from round-robin: the statement does not pin the policy.
// (2026-11-05: the scan reads a copy of `req` padded to 2^clog2(N) bits at the index (p + k) mod N, instead
// of `req[(32'(p) + k) % N]` in the first version, which ls-sv refuses (the cast) and the source checks refuse
// (a run-time index they cannot bound). Same policy, same grants. MEASURED: the reactive post-synthesis check
// passes it at N = 3 and 5 and REFUSES it at N = 8, where the scored netlist keeps a dead public-named wire of
// a techmapped cell with undriven bits, which the netlist lint rejects (tasks/arbiter/README.md, "Findings").)
// (2026-11-07: the clocked flow's last clean-up is `opt_clean -purge` (score/svgolf_seq.ys), which removes that
// wire; MEASURED: the netlist is lint-clean at N = 3, 5 and 8, with the same gates and GE, and the reactive check
// passes it at all three points: tests/checker/test_clocked_post.py.)
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
      p <= (p == N - 1) ? '0 : p + 1'b1;
    end
  end
endmodule
