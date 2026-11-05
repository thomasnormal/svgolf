module t #(parameter int N = 32) (input logic [N-1:0] d, output logic [N-1:0] y);
  assign y = {d[N-17:0], d[N-1:N-16]};
endmodule
