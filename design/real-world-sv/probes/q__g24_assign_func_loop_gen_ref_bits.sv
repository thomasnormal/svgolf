module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i++) begin : g
    assign y[i] = ^(a & {N{1'b1}});
  end
endmodule
