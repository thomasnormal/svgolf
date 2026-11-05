module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  logic [N:0][N-1:0] acc;
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : g
    assign acc[i+1] = acc[i] ^ (b[i] ? a : '0);
  end
  assign y = acc[N];
endmodule
