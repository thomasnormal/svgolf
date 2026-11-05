module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-2:0] p);
  logic [2*N-2:0][N-1:0] t;
  for (genvar k = 0; k < 2*N-1; k++) begin : c
    for (genvar i = 0; i < N; i++) begin : r
      // a[k-i] is read as 0 outside range by explicit padded vector
      logic [3*N-3:0] ap;
      assign ap = {{(N-1){1'b0}}, a, {(N-1){1'b0}}};
      assign t[k][i] = ap[N-1+k-i] & b[i];
    end
    assign p[k] = ^t[k];
  end
endmodule
