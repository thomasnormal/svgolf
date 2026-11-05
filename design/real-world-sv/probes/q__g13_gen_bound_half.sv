module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N/2-1:0] y);
  for (genvar i = 0; i < N/2; i++) begin : g
    assign y[i] = a[2*i] ^ a[2*i+1];
  end
endmodule
