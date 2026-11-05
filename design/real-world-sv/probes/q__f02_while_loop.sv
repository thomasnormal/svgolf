module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  always_comb begin
    int i;
    y = '0;
    i = 0;
    while (i < N) begin y = y | (a >> i); i = i + 1; end
  end
endmodule
