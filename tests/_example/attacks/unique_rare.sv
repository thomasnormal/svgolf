// svGolf attack (_example): unique_overlap.sv with the overlap confined to
// a[7:0] == 8'hEF && b == 16'h1234 (2^-24 of the inputs at N = 16). Refused by the
// source gate; postsynth alone catches it only through the harvested comparison
// constants (random vectors would need ~2^24 tries).
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    unique case (1'b1)
      (a[7:0] == 8'hEF): y = a & b;
      (b == 16'h1234):   y = a | b;
    endcase
  end
endmodule
