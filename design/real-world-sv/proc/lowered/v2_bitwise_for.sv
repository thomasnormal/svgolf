// for (i) p[i] = a[i] & b[i]  lowered as a generate of direct assigns (no SSA: distinct bits, no read)
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_lp
      assign p[i]   = a[i] & b[i];
      assign p[i+N] = a[i] ^ b[i];
    end
  endgenerate
endmodule
