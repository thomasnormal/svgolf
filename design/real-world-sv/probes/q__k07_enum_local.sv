module t #(parameter int N = 16) (input logic [1:0] o, input logic [7:0] a, b, output logic [7:0] y);
  typedef enum logic [1:0] {OP_AND, OP_OR, OP_XOR, OP_NOP} op_e;
  op_e op;
  assign op = op_e'(o);
  always_comb begin
    case (op)
      OP_AND: y = a & b;
      OP_OR:  y = a | b;
      OP_XOR: y = a ^ b;
      default: y = a;
    endcase
  end
endmodule
