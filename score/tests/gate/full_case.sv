// GATE: rejected. A pragma comment Yosys reads as full-case.
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  always_comb begin
    y = a & b;
    case (1'b0) // synopsys full_case
      1'b1: y = '0;
    endcase
  end
endmodule
