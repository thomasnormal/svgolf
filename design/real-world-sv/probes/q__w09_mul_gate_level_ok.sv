module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = {a[N-2:0], 1'b0} ^ {1'b0, a[N-1:1]};
endmodule
