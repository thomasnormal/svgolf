module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  logic [N-1:0] pp [N];
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i] = a & {N{b[i]}};
  end
  assign y = pp[0] ^ pp[N-1];
endmodule
