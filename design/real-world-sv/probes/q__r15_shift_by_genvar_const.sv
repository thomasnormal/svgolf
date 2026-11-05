module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  logic [N:0][N-1:0] st;
  assign st[0] = a;
  for (genvar i = 0; i < N; i++) begin : g
    assign st[i+1] = st[i] ^ (a << i);
  end
  assign y = st[N];
endmodule
