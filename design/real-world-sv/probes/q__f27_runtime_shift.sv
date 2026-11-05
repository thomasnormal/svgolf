module t #(parameter int N = 16) (input logic [N-1:0] a, input logic [$clog2(N)-1:0] s, output logic [N-1:0] y, z);
  assign y = a << s;
  assign z = a >> s;
endmodule
