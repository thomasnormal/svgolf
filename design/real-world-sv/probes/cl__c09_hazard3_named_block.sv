module clmul_n #(parameter N = 16) (input [N-1:0] a, b, output [2*N-2:0] p);
  reg [2*N-2:0] acc;
  always @(*) begin : mul
    integer i;
    acc = {2*N-1{1'b0}};
    for (i = 0; i < N; i = i + 1)
      acc = acc ^ (({{N-1{1'b0}}, a} << i) & {2*N-1{b[i]}});
  end
  assign p = acc;
endmodule
