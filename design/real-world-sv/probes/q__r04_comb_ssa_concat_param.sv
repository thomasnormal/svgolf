module t #(parameter int N = 32) (input logic [N-1:0] a, b, d, output logic [N-1:0] ra, rd);
  logic [N-1:0] a1, d1, d2;
  always_comb begin
    a1 = a + b;
    d1 = d ^ a1;
    d2 = {d1[15:0], d1[N-1:16]};
  end
  assign ra = a1;
  assign rd = d2;
endmodule
