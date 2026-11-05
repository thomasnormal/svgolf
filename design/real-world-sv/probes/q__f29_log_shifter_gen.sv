module t #(parameter int N = 16, parameter int L = 4) (input logic [N-1:0] a, input logic [L-1:0] s, output logic [N-1:0] y);
  logic [L:0][N-1:0] st;
  assign st[0] = a;
  for (genvar i = 0; i < L; i++) begin : g
    assign st[i+1] = s[i] ? (st[i] << (1 << i)) : st[i];
  end
  assign y = st[L];
endmodule
