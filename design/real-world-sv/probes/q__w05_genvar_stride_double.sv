module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y[0] = a[0];
  for (genvar i = 1; i < N; i = i * 2) begin : g
    assign y[i] = a[i];
  end
endmodule
