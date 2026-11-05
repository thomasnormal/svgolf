module t #(parameter int N = 8) (input logic [N-1:0] a, output logic [3:0] c);
  integer i;
  always_comb begin
    c = '0;
    for (i = 0; i < N; i = i + 1)
      c = c + a[i];
  end
endmodule
