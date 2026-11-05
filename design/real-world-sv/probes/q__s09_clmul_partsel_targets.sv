module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [N:0][2*N-2:0] acc;
  logic [N-1:0][2*N-2:0] pp;
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : r
    assign pp[i][i-1:0] = '0;
    assign pp[i][i+N-1:i] = a & {N{b[i]}};
    assign pp[i][2*N-2:i+N] = '0;
    assign acc[i+1] = acc[i] ^ pp[i];
  end
  assign p = acc[N];
endmodule
