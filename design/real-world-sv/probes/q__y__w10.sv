module t #(parameter int N=8) (input logic [N-1:0] a, output logic [3:0] c);
  always_comb begin
    c = '0;
    for (int i = 0; i < N; i++) c = c + {3'b0, a[i]};
  end
endmodule
