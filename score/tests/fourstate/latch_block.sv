// A variable an always_comb block reads before assigning it on every path: x in
// ls-sv and IEEE simulation (its initial value) where the path skips the
// assignment; Yosys refuses the process ("Latch inferred ... from always_comb").
module latch_block #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic r;
  always_comb begin
    if (a[0]) r = 1'b0;
    if (r) y = a | b;
    else y = a & b;
  end
endmodule
