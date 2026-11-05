module t #(parameter int N = 8) (input logic [N-1:0] a, output logic [N-1:0] y);
  always_comb begin
    for (int i = 0; i < N; i++) y[i] = a[N-1-i];
  end
endmodule
