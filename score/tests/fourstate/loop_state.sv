// A combinational loop that HOLDS STATE. The 4-state model resolves the start (`if (y)` with y = x takes the
// else branch), so ls-sv computes y = 0 for every stimulus and Terminates2 and Computes both hold with
// fn = const 0; the scored netlist is y = y & a, which has two stable states at a = 1. postsynth cannot see it
// (Verilator starts every vector from 0), so this stage is the only line: a retained loop is a latch.
// (docs/sv-tools-split-audit.md, probe loop_lat_if; design/nondeterminism/NOTE.md section 7)
module loop_state #(parameter int N = 4) (
  input  logic a,
  output logic y
);
  logic t;
  always_comb begin
    if (y) t = a; else t = 1'b0;
  end
  always_comb y = t;
endmodule
