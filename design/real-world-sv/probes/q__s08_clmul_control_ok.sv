module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [N:0][2*N-2:0] acc;
  logic [N-1:0][2*N-2:0] pp;
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : r
    for (genvar k = 0; k < 2*N-1; k++) begin : c
      if (k < i) begin : lo
        assign pp[i][k] = 1'b0;
      end else begin : hi
        assign pp[i][k] = 1'b0;
      end
    end
    assign acc[i+1] = acc[i] ^ pp[i];
  end
  assign p = acc[N];
endmodule
