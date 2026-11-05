module child #(parameter int W = 4) (input logic [W-1:0] x, output logic [W-1:0] z);
  assign z = ~x;
endmodule
module t #(parameter int N = 16) (input logic [N-1:0] a, output logic [N-1:0] y);
  child #(.W(N)) u (.x(a), .z(y));
endmodule
