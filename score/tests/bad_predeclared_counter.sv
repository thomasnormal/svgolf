// A pre-declared loop counter is constant only INSIDE its loop: here `k`
// holds a run-time value before the loop, and `k + 1` is a run-time adder.
module bad_predeclared_counter #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y,
  output logic [N-1:0] z
);
  integer k;
  always_comb begin
    k = a;
    z = k + 1;
    for (k = 0; k < N; k = k + 1) y[k] = a[k] & b[k];
  end
endmodule
