// STYLE: one XOR-reduction per output column, `p[k] = ^(a & window of the reversed b)`: the column sum as an
// AND followed by the unary reduction `^` (the "x^y reduction operator" form), with an indexed part select
// of a zero-padded reversed copy of b.
// Correct for every N; scored as written.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [N-1:0]     brev;
  logic [3*N-3:0]   bpad;     // {N-1 zeros, reversed b, N-1 zeros}
  genvar i, k;
  generate
    for (i = 0; i < N; i++) begin : g_rev
      assign brev[i] = b[N-1-i];
    end
    for (i = 0; i < N-1; i++) begin : g_pad
      assign bpad[i] = 1'b0;
      assign bpad[2*N-1+i] = 1'b0;
    end
    for (i = 0; i < N; i++) begin : g_mid
      assign bpad[N-1+i] = brev[i];
    end
    for (k = 0; k < 2*N-1; k++) begin : g_col
      assign p[k] = ^(a & bpad[(2*N-2-k) +: N]);
    end
  endgenerate
endmodule
