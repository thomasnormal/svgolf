// svGolf attack (_example): a `unique0 case` that never matches (parallel_case only).
// Benign: the netlist is a & b like ls-sv's reading. Refused by the source gate;
// postsynth alone finds no difference.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    unique0 case (1'b1)
      (a[0] & ~a[0]): y = '0;
    endcase
  end
endmodule
