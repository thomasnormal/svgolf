// SHAPE probe: a one-bit accumulator chain (parity of the selected bits), an always_comb if/else per iteration
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N:0] par;
  assign par[0] = 1'b0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : lp_par
      always_comb begin
        if (b[i]) par[i+1] = par[i] ^ a[i];
        else      par[i+1] = par[i];
      end
    end
  endgenerate
  assign p[0] = par[N];
  assign p[2*N-1:1] = '0;
endmodule
