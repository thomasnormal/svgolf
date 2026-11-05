module acc_if #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++) if (b[i]) p = p ^ a;
  end
endmodule
