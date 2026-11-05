module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i++) begin : g
    logic w;
    assign w = a[i] & b[i];
    assign y[i] = w;
  end
endmodule
