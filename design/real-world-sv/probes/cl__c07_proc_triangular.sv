module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  always_comb begin
    p = '0;
    for (integer k = 0; k < 2*N-1; k++)
      for (integer j = 0; j <= k; j++)
        if (j < N && k - j < N) p[k] = p[k] ^ (a[k-j] & b[j]);
  end
endmodule
