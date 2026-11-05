package pk;
  typedef enum logic [1:0] {OP_AND, OP_OR, OP_XOR, OP_NOP} op_e;
  localparam int W = 8;
endpackage
import pk::*;
module t (input logic [1:0] opc, input logic [W-1:0] a, b, output logic [W-1:0] y);
  op_e op;
  assign op = op_e'(opc);
  always_comb begin
    case (op)
      OP_AND: y = a & b;
      OP_OR:  y = a | b;
      OP_XOR: y = a ^ b;
      default: y = a;
    endcase
  end
endmodule
