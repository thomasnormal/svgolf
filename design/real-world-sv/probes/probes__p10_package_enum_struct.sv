package alu_pkg;
  typedef enum logic [1:0] {ADD, XOR_, AND_, OR_} op_e;
  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;
  localparam int W = 8;
endpackage
module t import alu_pkg::*; (input op_e op, input pair_t x, output logic [W-1:0] y);
  always_comb begin
    case (op)
      ADD: y = x.a ^ x.b;
      XOR_: y = x.a & x.b;
      AND_: y = x.a | x.b;
      default: y = x.a;
    endcase
  end
endmodule
