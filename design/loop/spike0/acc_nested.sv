module acc_nested #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++)
      for (int j = 0; j < N; j++)
        p[i+j] = p[i+j] ^ (a[i] & b[j]);
  end
endmodule
