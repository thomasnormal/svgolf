module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam int R = 7;
  assign y = {a[R-1:0], a[N-1:R]};
endmodule
