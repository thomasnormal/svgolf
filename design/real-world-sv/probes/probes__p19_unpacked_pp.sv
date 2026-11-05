module t #(parameter int N = 8) (input logic [N-1:0] a, b, output logic [2*N-1:0] p);
  logic [2*N-1:0] pp [N];
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i] = b[i] ? (2*N)'(a) << i : '0;
  end
  logic [2*N-1:0] acc [N+1];
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : h
    assign acc[i+1] = acc[i] ^ pp[i];
  end
  assign p = acc[N];
endmodule
