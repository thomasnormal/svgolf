module t #(parameter int N = 16) (input logic [N-1:0] a, input logic [$clog2(N)-1:0] s, output logic [N-1:0] y);
  logic [2*N-1:0] d;
  assign d = {a, a};
  logic [2*N-1:0] r;
  assign r = d >> s;
  assign y = r[N-1:0];
endmodule
