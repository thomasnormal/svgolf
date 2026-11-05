// GATE: rejected. As unique_case.sv, with priority (Yosys: full-case).
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
