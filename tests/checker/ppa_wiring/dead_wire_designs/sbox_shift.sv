// WP-X3 review: an aes_sbox design whose scored netlist carries the dead public-named wires of techmapped cells (a run-time shift, a one-hot decode, a bit select).
// Not a task reference: tests/checker/test_ppa_wiring.py runs it through check.py's stages (fake Lean) and expects ppa.available = true.
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
  assign y = (x >> x[2:0]) ^ (x << x[1:0]) ^ 8'h63;
endmodule
