// Priority encoder over N bits (WS3 loop-shape sizing, design (a)): one-level loop, an `if` in the
// body, a `<=` header against the parameter. y = 1 + the index of the highest set bit of a, or 0.
module prienc #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [31:0]  y
);
  always_comb begin
    y = '0;
    for (int i = 1; i <= N; i++)
      if (a[i-1]) y = i;
  end
endmodule
