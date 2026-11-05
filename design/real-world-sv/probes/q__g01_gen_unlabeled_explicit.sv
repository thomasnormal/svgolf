module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  genvar i;
  generate
    for (i = 0; i < N; i = i + 1) begin
      assign y[i] = a[i] ^ b[i];
    end
  endgenerate
endmodule
