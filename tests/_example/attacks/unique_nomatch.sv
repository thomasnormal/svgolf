// svGolf attack (_example): a `unique case` that never matches, after y = a & b.
// ls-sv runs no arm: y = a & b. Yosys reads `unique` as full_case + parallel_case
// and drives y with x (0 GE). The source gate refuses `unique`; postsynth alone (the
// gate's refusal lifted) rejects it on every vector.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    unique case (1'b1)
      (a[0] & ~a[0]): y = '0;
    endcase
  end
endmodule
