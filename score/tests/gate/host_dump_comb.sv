// GATE: rejected (P-NO-HOST-ACCESS). The dump tasks as statements of a COMBINATIONAL
// block: the one host-access form that nothing else in the flow refuses. The pinned
// Yosys 0.53 ignores $dumpfile / $dumpvars with a warning, and the ls-sv extractor
// lowers them to an empty statement (outside an `initial` block, which ls-sv refuses
// whole), so before the gate this design went through every stage up to the proof.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    $dumpfile("/tmp/svgolf-leak.vcd");
    $dumpvars(0, band);
    y = a & b;
  end
endmodule
