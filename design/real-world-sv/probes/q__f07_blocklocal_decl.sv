module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  always_comb begin
    logic [N-1:0] t1;
    t1 = a ^ b;
    y = t1 & a;
  end
endmodule
