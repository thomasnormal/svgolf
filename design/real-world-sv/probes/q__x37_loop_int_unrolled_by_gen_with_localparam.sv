module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam int H = (N + 1) / 2;
  for (genvar i = 0; i < H; i++) begin : g
    assign y[i] = a[i];
  end
  for (genvar i = H; i < N; i++) begin : h
    assign y[i] = ~a[i];
  end
endmodule
