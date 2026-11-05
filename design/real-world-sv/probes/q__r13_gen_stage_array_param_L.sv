module t #(parameter int N = 16) (input logic [N-1:0] a, input logic [3:0] s, output logic [N-1:0] y);
  localparam int L = 4;
  logic [L:0][N-1:0] st;
  assign st[0] = a;
  for (genvar i = 0; i < L; i++) begin : g
    assign st[i+1] = s[i] ? (st[i] << (1 << i)) : st[i];
  end
  assign y = st[L];
endmodule
