module m4 #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++) if (b[i]) p = p ^ (a << i);
  end
endmodule
