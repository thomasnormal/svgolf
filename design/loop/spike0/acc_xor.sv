module acc_xor #(parameter int N = 4) (input logic [N-1:0] a, output logic p);
  always_comb begin
    p = 1'b0;
    for (int i = 0; i < N; i++) p = p ^ a[i];
  end
endmodule
