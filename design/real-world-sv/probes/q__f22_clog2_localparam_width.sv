module t #(parameter int N = 16) (input logic [N-1:0] a, input logic [$clog2(N)-1:0] s, output logic y);
  localparam int L = $clog2(N);
  logic [L-1:0] s2;
  assign s2 = s;
  assign y = a[s2];
endmodule
