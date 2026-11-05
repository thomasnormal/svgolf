module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [2*N-2:0] pp  [N];
  logic [2*N-2:0] acc [N+1];
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i]  = b[i] ? ((2*N-1)'(a) << i) : '0;
    assign acc[i+1] = acc[i] ^ pp[i];
  end
  assign p = acc[N];
endmodule
