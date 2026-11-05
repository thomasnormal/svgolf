// SHAPE probe: row chain with N-wide rows (r16 shape) as a continuous ?: assign in a family
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N:0][N-1:0] acc;
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : lp_acc
      assign acc[i+1] = b[i] ? (acc[i] ^ a) : acc[i];
    end
  endgenerate
  assign p[N-1:0]   = acc[N];
  assign p[2*N-1:N] = '0;
endmodule
