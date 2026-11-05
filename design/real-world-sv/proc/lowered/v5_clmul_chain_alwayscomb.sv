// the proposed lowering of the natural clmul loop: SSA chain in a packed 2-D row array, each iteration an
// always_comb if/else (the add_proc carry-cell shape), the shift inline
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N:0][2*N-1:0] p__1;
  assign p__1[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : lp_p
      always_comb begin
        if (b[i]) p__1[i+1] = p__1[i] ^ (a << i);
        else      p__1[i+1] = p__1[i];
      end
    end
  endgenerate
  assign p = p__1[N];
endmodule
