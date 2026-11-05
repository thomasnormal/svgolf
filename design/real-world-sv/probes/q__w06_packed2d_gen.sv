module t #(parameter int N = 16) (input logic [N-1:0][N-1:0] p, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i++) begin : g
    assign y[i] = ^p[i];
  end
endmodule
