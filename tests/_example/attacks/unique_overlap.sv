// svGolf attack (_example): a `unique case (1'b1)` with overlapping items a[1], a[0].
// ls-sv runs the first matching arm; Yosys's parallel_case ORs both arms where both
// match (a different function on a quarter of the inputs). Refused by the source gate;
// postsynth alone rejects it.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    unique case (1'b1)
      a[1]: y = a & b;
      a[0]: y = a | b;
    endcase
  end
endmodule
