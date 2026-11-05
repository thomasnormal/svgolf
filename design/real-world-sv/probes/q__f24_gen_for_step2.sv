module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i += 2) begin : g
    assign y[i] = a[i] ^ b[i];
    if (i + 1 < N) begin : h
      assign y[i+1] = a[i+1] & b[i+1];
    end
  end
endmodule
