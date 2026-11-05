module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [2*N-2:0] acc;
  always_comb begin
    acc = '0;
    for (int i = 0; i < N; i++)
      if (b[i]) acc = acc ^ ({{(N-1){1'b0}}, a} << i);
    p = acc;
  end
endmodule
