module clmul_n #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  // hand-unrolled 4 terms (N = 4 only): ternary of shifted operand
  assign p = (b[0] ? {3'b0, a}      : '0) ^
             (b[1] ? {2'b0, a, 1'b0} : '0) ^
             (b[2] ? {1'b0, a, 2'b0} : '0) ^
             (b[3] ? {a, 3'b0}       : '0);
endmodule
