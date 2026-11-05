// SHAPE probe: 2N-wide rows, row written by a plain assign without ?: (is the row width 2*N the problem?)
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
  logic [N:0][2*N-1:0] acc;
  logic [2*N-1:0] ae;
  assign ae[N-1:0]   = a;
  assign ae[2*N-1:N] = '0;
  assign acc[0] = '0;
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : lp_acc
      assign acc[i+1] = acc[i] ^ ae;
    end
  endgenerate
  assign p = acc[N];
endmodule
