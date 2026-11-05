// SHAPE probe: row chain with N-wide rows, always_comb if/else per iteration (the r16 shape)
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N:0][N-1:0] acc;
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : lp_acc
      always_comb begin
        if (b[i]) acc[i+1] = acc[i] ^ a;
        else      acc[i+1] = acc[i];
      end
    end
  endgenerate
  assign p[N-1:0]   = acc[N];
  assign p[2*N-1:N] = '0;
endmodule
