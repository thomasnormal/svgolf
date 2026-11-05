module t #(parameter int N = 4) (input logic [N*N-1:0] a, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i++) begin : g
    for (genvar j = 0; j < N; j++) begin : h
      if (j == 0) begin : z
        assign y[i] = a[i*N+j];
      end
    end
  end
endmodule
