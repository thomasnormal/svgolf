// The same never-loaded latch spelled `always_latch`: refused by the same rule (ls-sv does not model it either).
module latch_always_latch #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic r;
  always_latch begin
    if (a[0] & ~a[0]) r = 1'b1;
  end
  always_comb begin
    if (!r) y = a | b;
    else y = a & b;
  end
endmodule
