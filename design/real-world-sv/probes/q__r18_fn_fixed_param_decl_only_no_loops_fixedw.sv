module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  logic [N:0][N-1:0] acc;
  logic [N-1:0] zero;
  assign zero = '0;
  assign acc[0] = zero;
  for (genvar i = 0; i < N; i++) begin : g
    assign acc[i+1] = acc[i] ^ (a & {N{b[i]}});
  end
  assign y = acc[N];
endmodule
