// STYLE: word-wide partial products with a zero-fill loop that starts at N (a natural way to write the padding):
// `for (i = N; i < 2*N-1; i++) assign aw[i] = 1'b0;`. Everything before the proof accepts it; the sv_comb
// tactics' generate-for header is `for (g = <int>; g < <affine>; g++)`: the start must be an integer literal.
// Correct for every N.
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
  logic [2*N-2:0] aw;
  logic [N-1:0][2*N-2:0] pp;
  logic [N:0][2*N-2:0]   acc;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_a
      assign aw[i] = a[i];
    end
    for (i = N; i < 2*N-1; i++) begin : g_z
      assign aw[i] = 1'b0;
    end
  endgenerate
  assign acc[0] = '0;
  generate
    for (i = 0; i < N; i++) begin : g_pp
      assign pp[i]    = b[i] ? (aw << i) : '0;
      assign acc[i+1] = acc[i] ^ pp[i];
    end
  endgenerate
  assign p = acc[N];
endmodule
