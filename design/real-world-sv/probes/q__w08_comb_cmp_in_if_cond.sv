module t #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  always_comb begin
    if (a >= b) y = a - b;
    else y = a;
  end
endmodule
