module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  // coefficient form, bit level: row i contributes a[j]&b[i] to p[i+j]
  logic [N:0][2*N-2:0] acc;
  assign acc[0] = '0;
  for (genvar i = 0; i < N; i++) begin : r
    for (genvar k = 0; k < 2*N-1; k++) begin : c
      if (k >= i && k - i < N) begin : hit
        assign acc[i+1][k] = acc[i][k] ^ (a[k-i] & b[i]);
      end else begin : miss
        assign acc[i+1][k] = acc[i][k];
      end
    end
  end
  assign p = acc[N];
endmodule
