module t #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  logic [N-1:0] z;
  for (genvar i = 0; i < N; i++) begin : g1
    for (genvar j = 0; j < 1; j++) begin : g2
      for (genvar k = 0; k < 1; k++) begin : g3
        assign z[i] = a[i];
      end
    end
  end
  assign y = z;
endmodule
