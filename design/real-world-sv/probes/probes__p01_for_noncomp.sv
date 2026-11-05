module t #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [2*N-1:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++)
      if (b[i]) p = p ^ ((2*N)'(a) << i);
  end
endmodule
