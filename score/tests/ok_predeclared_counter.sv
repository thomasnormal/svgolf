// A pre-declared integer as a procedural loop counter: constant in the loop.
module ok_predeclared_counter #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
  integer k;
  always_comb begin
    y = '0;
    for (k = 0; k < N - 1; k = k + 1) y[k + 1] = a[k] & b[k + 1];
  end
endmodule
