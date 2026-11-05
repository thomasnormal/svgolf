// WS3 negative fixture (own code, not ibex): a latch-style `always_comb`. `q` is written only when
// `en` is set, so the written-before-read check (`CombSlotE.combWbr`) refuses the body.
module x7_latch (
  input  logic en,
  input  logic [3:0] d,
  output logic [3:0] q
);
  always_comb begin
    if (en) q = d;
  end
endmodule
