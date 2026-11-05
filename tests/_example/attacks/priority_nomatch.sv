// svGolf attack (_example): a `priority case` that never matches, after y = a & b.
// As unique_nomatch.sv: refused by the source gate; postsynth alone rejects it.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    priority case (1'b1)
      (a[0] & ~a[0]): y = '0;
    endcase
  end
endmodule
