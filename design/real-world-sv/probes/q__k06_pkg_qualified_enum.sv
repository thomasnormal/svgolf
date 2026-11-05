package pk;
  typedef enum logic [1:0] {OP_AND, OP_OR} op_e;
endpackage
module t #(parameter int N = 16) (input logic [1:0] o, input logic [7:0] a, b, output logic [7:0] y);
  pk::op_e op;
  assign op = pk::op_e'(o);
  assign y = (op == pk::OP_AND) ? a & b : a | b;
endmodule
