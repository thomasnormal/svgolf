module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  for (genvar i = 0; i < N; i++) begin : g
    if (i % 2 == 0) begin : ev
      assign y[i] = a[i] & b[i];
    end else begin : od
      assign y[i] = a[i] | b[i];
    end
  end
endmodule
