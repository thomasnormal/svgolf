// GATE: rejected. An attribute: Yosys gives (* full-case *) a synthesis meaning.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    (* full_case *)
    case (1'b0)
      1'b1: y = '0;
    endcase
  end
endmodule
