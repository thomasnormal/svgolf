module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++)
      if (b[i]) p ^= (2*N-1)'(a) << i;
  end
endmodule
