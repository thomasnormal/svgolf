module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [2*N-2:0] ext;
  assign ext = {{(N-1){1'b0}}, a};
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++)
      if ((b >> i) & 1'b1) p = p ^ (ext << i);
  end
endmodule
