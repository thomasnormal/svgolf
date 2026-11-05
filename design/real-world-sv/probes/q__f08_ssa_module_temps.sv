module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  logic [N-1:0] t1, t2;
  always_comb begin
    t1 = a ^ b;
    t2 = t1 & a;
    y = t2 | b;
  end
endmodule
