// svGolf attack (_example): a `unique case` whose first item is the constant 1.
// The netlist is a & b. Refused by the source gate. Whenever a[0]=1 both items match, a `unique`
// violation, which ls-sv reports loudly (CaseCheck, master 2218821b), so postsynth alone rejects it too.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = '0;
    unique case (1'b1)
      1'b1: y = a & b;
      a[0]: y = a | b;
    endcase
  end
endmodule
