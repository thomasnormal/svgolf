module t #(parameter int N = 16, localparam int L = $clog2(N)) (input logic [N-1:0] a, input logic [L-1:0] s, output logic y);
  assign y = a[s];
endmodule
