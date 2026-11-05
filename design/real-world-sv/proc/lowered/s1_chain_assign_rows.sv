// SHAPE probe: the row-valued SSA chain with the phi written as a continuous ?: assign (rows in a family)
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [2*N-1:0] ae;
  assign ae[N-1:0]   = a;
  assign ae[2*N-1:N] = '0;
  logic [N:0][2*N-1:0] p__1;
  assign p__1[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : lp_p
      assign p__1[i+1] = b[i] ? (p__1[i] ^ ae) : p__1[i];
    end
  endgenerate
  assign p = p__1[N];
endmodule
